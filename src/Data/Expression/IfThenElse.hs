{-# LANGUAGE FlexibleContexts
           , FlexibleInstances
           , GADTs
           , InstanceSigs
           , MultiParamTypeClasses
           , OverloadedStrings
           , RankNTypes
           , ScopedTypeVariables
           , TypeInType
           , TypeOperators #-}

--------------------------------------------------------------------------------
-- |
-- Module     :  Data.Expression.IfThenElse
-- Copyright  :  (C) 2017-18 Jakub Daniel
-- License    :  BSD-style (see the file LICENSE)
-- Maintainer :  Jakub Daniel <jakub.daniel@protonmail.com>
-- Stability  :  experimental
--------------------------------------------------------------------------------

module Data.Expression.IfThenElse ( IfThenElseF(..)
                                  , ite ) where

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

-- | A functor representing a conditional value (if-then-else)
data IfThenElseF a (s :: Sort) where
    IfThenElse :: Sing s -> a 'BooleanSort -> a s -> a s -> IfThenElseF a s

instance IEq1 IfThenElseF where
    IfThenElse sa ia ta ea `ieq1` IfThenElse sb ib tb eb = ia `ieq` ib && case sa %~ sb of
        Proved Refl -> ta `ieq` tb && ea `ieq` eb
        Disproved _ -> False

instance IFunctor IfThenElseF where
    imap f (IfThenElse s i t e) = IfThenElse s (f i) (f t) (f e)
    index (IfThenElse s _ _ _) = s

instance IFoldable IfThenElseF where
    ifold :: forall m (s :: Sort). Monoid m => IfThenElseF (Const m) s -> Const m s
    ifold (IfThenElse _ i t e) = coerce ((coerce i <> coerce t <> coerce e) :: m)

instance ITraversable IfThenElseF where
    itraverse f (IfThenElse s i t e) = IfThenElse s <$> f i <*> f t <*> f e

instance IShow IfThenElseF where
    ishow (IfThenElse _ i t e) = coerce $ "(ite " ++ coerce i ++ " " ++ coerce t ++ " " ++ coerce e ++ ")"

instance IfThenElseF :<: f => Parseable IfThenElseF f where
    parser _ r = do
        _ <- char '(' *> string "ite" *> space
        i <- r
        _ <- space
        t <- r
        _ <- space
        e <- r
        _ <- char ')'
        ifThenElse i t e <?> "IfThenElse" where

        ifThenElse :: DynamicallySorted f -> DynamicallySorted f -> DynamicallySorted f -> Parser (DynamicallySorted f)
        ifThenElse (DynamicallySorted s1 i)
                   (DynamicallySorted s2 t)
                   (DynamicallySorted s3 e) = case s1 %~ SBooleanSort of
            Proved Refl -> case s2 %~ s3 of
                Proved Refl -> return . DynamicallySorted s2 $ inject (IfThenElse s2 i t e)
                Disproved _ -> fail "inconsistent sorts of then and else branches"
            Disproved _ -> fail "branching on non-boolean expression"

-- | A smart constructor for an if-then-else expression
ite :: forall f s. ( IfThenElseF :<: f, SingI s ) => IFix f 'BooleanSort -> IFix f s -> IFix f s -> IFix f s
ite i t e = inject (IfThenElse (sing :: Sing s) i t e)
