{-# LANGUAGE FlexibleContexts
           , FlexibleInstances
           , GADTs
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
                             , store ) where

import Data.Functor.Const
import Data.Singletons
import Data.Singletons.Decide

import Data.Expression.Parser
import Data.Expression.Sort
import Data.Expression.Utils.Indexed.Functor
import Data.Expression.Utils.Indexed.Show
import Data.Expression.Utils.Indexed.Sum

-- | A functor representing array-theoretic terms (`select` and `store` also known as "read" and "write")
data ArrayF a (s :: Sort) where
    Select :: Sing i -> a ('ArraySort i e) -> a i        -> ArrayF a e
    Store  ::           a ('ArraySort i e) -> a i -> a e -> ArrayF a ('ArraySort i e)

instance IFunctor ArrayF where
    imap f (Select s a i)   = Select s (f a) (f i)
    imap f (Store    a i e) = Store    (f a) (f i) (f e)

instance IShow ArrayF where
    ishow (Select _ a i)   = Const $ "(select " ++ getConst a ++ " " ++ getConst i ++ ")"
    ishow (Store    a i v) = Const $ "(store " ++ getConst a ++ " " ++ getConst i ++ " " ++ getConst v ++ ")"

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

        select'' :: DynamicallySorted f -> DynamicallySorted f -> Parser (DynamicallySorted f)
        select'' (DynamicallySorted (SArraySort is1 es) a)
                 (DynamicallySorted is2                 i) = case is1 %~ is2 of
            Proved Refl -> return . DynamicallySorted es $ inject (Select is1 a i)
            Disproved _ -> fail "ill-sorted select"
        select'' _ _ = fail "selecting from non-array"

        store'' :: DynamicallySorted f -> DynamicallySorted f -> DynamicallySorted f -> Parser (DynamicallySorted f)
        store''  (DynamicallySorted as@(SArraySort _ _) a)
                 (DynamicallySorted is                  i)
                 (DynamicallySorted es                  v) = case as %~ SArraySort is es of
            Proved Refl -> return . DynamicallySorted as $ store a i v
            Disproved _ -> fail "ill-sorted store"
        store'' _ _ _ = fail "storing to non-array"

-- | A smart constructor for select
select :: forall f i e. ( ArrayF :<: f, SingI i ) => IFix f ('ArraySort i e) -> IFix f i -> IFix f e
select a i = inject (Select (sing :: Sing i) a i)

-- | A smart constructor for store
store :: ArrayF :<: f => IFix f ('ArraySort i e) -> IFix f i -> IFix f e -> IFix f ('ArraySort i e)
store a i v = inject (Store a i v)
