{-# LANGUAGE DerivingVia
           , FlexibleContexts
           , FlexibleInstances
           , GADTs
           , LiberalTypeSynonyms
           , MultiParamTypeClasses
           , OverloadedStrings
           , RankNTypes
           , ScopedTypeVariables
           , TypeInType
           , TypeOperators #-}

--------------------------------------------------------------------------------
-- |
-- Module     :  Data.Expression.Array
-- Copyright  :  (C) 2017-18 Jakub Daniel
-- License    :  BSD-style (see the file LICENSE)
-- Maintainer :  Jakub Daniel <jakub.daniel@protonmail.com>
-- Stability  :  experimental
--------------------------------------------------------------------------------

module Data.Expression.Array ( ArrayF(..)
                             , select
                             , store
                             , accesses
                             , toStaticallySortedArrayAccess
                             , ArrayAccess(..)
                             , DynamicValueArrayAccess(..)
                             , DynamicArrayAccess ) where

import Control.Monad
import Control.Monad.Trans.Writer
import Data.Coerce
import Data.Functor.Const
import Data.Singletons
import Data.Singletons.Decide

import Data.Expression.Parser
import Data.Expression.Sort
import Data.Expression.Utils.Indexed.Eq
import Data.Expression.Utils.Indexed.Foldable
import Data.Expression.Utils.Indexed.Functor
import Data.Expression.Utils.Indexed.Show
import Data.Expression.Utils.Indexed.Sum
import Data.Expression.Utils.Indexed.Traversable

-- | A functor representing array-theoretic terms (`select` and `store` also known as "read" and "write")
data ArrayF a (s :: Sort) where
    Select :: Sing i -> Sing e -> a ('ArraySort i e) -> a i        -> ArrayF a e
    Store  :: Sing i -> Sing e -> a ('ArraySort i e) -> a i -> a e -> ArrayF a ('ArraySort i e)

instance IEq1 ArrayF where
    Select isa _ aa ia `ieq1` Select isb _ ab ib = case isa %~ isb of
        Proved Refl -> aa `ieq` ab && ia `ieq` ib
        Disproved _ -> False
    Store _ _ aa ia va `ieq1` Store _ _ ab ib vb = aa `ieq` ab && ia `ieq` ib && va `ieq` vb
    _                  `ieq1` _                  = False

instance IFunctor ArrayF where
    imap f (Select is es a i)   = Select is es (f a) (f i)
    imap f (Store  is es a i e) = Store  is es (f a) (f i) (f e)

    index (Select _  es _ _  ) = es
    index (Store  is es _ _ _) = SArraySort is es

instance IFoldable ArrayF where
    ifold (Select _ _ a i)   = coerce a <> coerce i
    ifold (Store  _ _ a i e) = coerce a <> coerce i <> coerce e

instance ITraversable ArrayF where
    itraverse f (Select is es a i)   = Select is es <$> f a <*> f i
    itraverse f (Store  is es a i e) = Store  is es <$> f a <*> f i <*> f e

instance IShow ArrayF where
    ishow (Select _ _ a i)   = coerce $ "(select " ++ coerce a ++ " " ++ coerce i ++ ")"
    ishow (Store  _ _ a i v) = coerce $ "(store " ++ coerce a ++ " " ++ coerce i ++ " " ++ coerce v ++ ")"

instance ArrayF :<: f => Parseable ArrayF f where
    parser _ r = choice [ select', store' ] <?> "Array" where
        select' = do
            _ <- char '(' *> string "select" *> space
            a <- r
            _ <- space
            i <- r
            _ <- char ')'
            select'' a i
        store' = do
            _ <- char '(' *> string "store"  *> space
            a <- r
            _ <- space
            i <- r
            _ <- space
            v <- r
            _ <- char ')'
            store'' a i v

        select'' :: DynamicallySortedFix f -> DynamicallySortedFix f -> Parser (DynamicallySortedFix f)
        select'' (DynamicallySorted (SArraySort is1 es) a)
                 (DynamicallySorted is2                 i) = case is1 %~ is2 of
            Proved Refl -> return . DynamicallySorted es $ inject (Select is1 es a i)
            Disproved _ -> fail "ill-sorted select"
        select'' _ _ = fail "selecting from non-array"

        store'' :: DynamicallySortedFix f -> DynamicallySortedFix f -> DynamicallySortedFix f -> Parser (DynamicallySortedFix f)
        store''  (DynamicallySorted as@(SArraySort _ _) a)
                 (DynamicallySorted is                  i)
                 (DynamicallySorted es                  v) = case as %~ SArraySort is es of
            Proved Refl -> return . DynamicallySorted as $ inject (Store is es a i v)
            Disproved _ -> fail "ill-sorted store"
        store'' _ _ _ = fail "storing to non-array"

-- | A smart constructor for select
select :: ( ArrayF :<: f, SingI i, SingI e ) => IFix f ('ArraySort i e) -> IFix f i -> IFix f e
select a i = inject (Select sing sing a i)

-- | A smart constructor for store
store :: ( ArrayF :<: f, SingI i, SingI e ) => IFix f ('ArraySort i e) -> IFix f i -> IFix f e -> IFix f ('ArraySort i e)
store a i v = inject (Store sing sing a i v)

type Array f (e :: Sort) (i :: Sort) = IFix f ('ArraySort i e)
type Index f (i :: Sort)             = IFix f i

newtype ArrayAccess             f (i :: Sort) (e :: Sort) = ArrayAccess             { getAA   :: (Array f e i, Index f i) }            deriving Show via (Array f e i, Index f i)
newtype DynamicValueArrayAccess f (i :: Sort)             = DynamicValueArrayAccess { getDVAA :: DynamicallySorted (ArrayAccess f i) } deriving Show via (DynamicallySorted (ArrayAccess f i))
type    DynamicArrayAccess      f                         = DynamicallySorted (DynamicValueArrayAccess f)

-- | Tries to convert access to an array of some sort to an access to an array of a specific sort
toStaticallySortedArrayAccess :: forall f (i :: Sort) (e :: Sort). ( SingI i, SingI e ) => DynamicArrayAccess f -> Maybe (IFix f ('ArraySort i e), IFix f i)
toStaticallySortedArrayAccess = elementSort <=< indexSort where
  elementSort :: DynamicallySorted (ArrayAccess f i) -> Maybe (Array f e i, Index f i)
  elementSort = fmap getAA . toStaticallySorted

  indexSort :: DynamicArrayAccess f -> Maybe (DynamicallySorted (ArrayAccess f i))
  indexSort = fmap getDVAA . toStaticallySorted

-- | Collects pairs of arrays and indices that appear together in some @select@ and/or @store@ within an expression
accesses :: forall f (s :: Sort). ( ArrayF :<: f, ITraversable f ) => IFix f s -> [DynamicArrayAccess f]
accesses = execWriter . imapM accesses' where
  accesses' :: forall (s' :: Sort). IFix f s' -> Writer [DynamicArrayAccess f] (IFix f s')
  accesses' e = do
    case match e of
      Just (Select is es a i)   -> tell [ DynamicallySorted is
                                        $ DynamicValueArrayAccess
                                        $ DynamicallySorted es
                                        $ ArrayAccess
                                        $ (a, i) ]
      Just (Store  is es a i _) -> tell [ DynamicallySorted is
                                        $ DynamicValueArrayAccess
                                        $ DynamicallySorted es
                                        $ ArrayAccess
                                        $ (a, i) ]
      _                         -> return ()
    return e
