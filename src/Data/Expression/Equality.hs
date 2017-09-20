{-# LANGUAGE DataKinds
           , FlexibleContexts
           , FlexibleInstances
           , GADTs
           , MultiParamTypeClasses
           , RankNTypes
           , ScopedTypeVariables
           , TypeInType
           , TypeOperators #-}

--------------------------------------------------------------------------------
-- |
-- Module     :  Data.Expression.Equality
-- Copyright  :  (C) 2017-18 Jakub Daniel
-- License    :  BSD-style (see the file LICENSE)
-- Maintainer :  Jakub Daniel <jakub.daniel@protonmail.com>
-- Stability  :  experimental
--------------------------------------------------------------------------------

module Data.Expression.Equality ( EqualityF(..)
                                , (.=.) ) where

import Data.Functor.Const
import Data.Singletons
import Data.Singletons.Decide

import Data.Expression.Parser
import Data.Expression.Sort
import Data.Expression.Utils.Indexed.Functor
import Data.Expression.Utils.Indexed.Show
import Data.Expression.Utils.Indexed.Sum

-- | A functor representing an equality predicate between two expressions of matching sort
data EqualityF a (s :: Sort) where
    Equals :: Sing s -> a s -> a s -> EqualityF a 'BooleanSort

instance IFunctor EqualityF where
    imap f (Equals s a b) = Equals s (f a) (f b)

instance IShow EqualityF where
    ishow (Equals _ a b) = Const $ "(= " ++ getConst a ++ " " ++ getConst b ++ ")"

instance EqualityF :<: f => Parseable EqualityF f where
    parser _ r = do
        _ <- char '(' *> char '=' *> space
        a <- r
        _ <- space
        b <- r
        _ <- char ')'
        equals a b <?> "Equality" where

        equals :: DynamicallySorted f -> DynamicallySorted f -> Parser (DynamicallySorted f)
        equals (DynamicallySorted s1 a)
               (DynamicallySorted s2 b) = case s1 %~ s2 of
            Proved Refl -> return . DynamicallySorted SBooleanSort $ inject (Equals s1 a b)
            Disproved _ -> fail "multi-sorted equality"

-- | A smart constructor for an equality predicate
(.=.) :: forall f s. ( EqualityF :<: f, SingI s ) => IFix f s -> IFix f s -> IFix f 'BooleanSort
a .=. b = inject (Equals (sing :: Sing s) a b)

infix 7 .=.
