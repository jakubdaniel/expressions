{-# LANGUAGE FlexibleContexts
           , FlexibleInstances
           , GADTs
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

import Data.Functor.Const
import Data.Singletons

import Data.Expression.Sort
import Data.Expression.Utils.Indexed.Functor
import Data.Expression.Utils.Indexed.Show
import Data.Expression.Utils.Indexed.Sum

-- | A functor representing a conditional value (if-then-else)
data IfThenElseF a (s :: Sort) where
    IfThenElse :: Sing s -> a 'BooleanSort -> a s -> a s -> IfThenElseF a s

instance IFunctor IfThenElseF where
    imap f (IfThenElse s i t e) = IfThenElse s (f i) (f t) (f e)

instance IShow IfThenElseF where
    ishow (IfThenElse _ i t e) = Const $ "(ite " ++ getConst i ++ " " ++ getConst t ++ " " ++ getConst e ++ ")"

-- | A smart constructor for an if-then-else expression
ite :: forall f s. ( IfThenElseF :<: f, SingI s ) => IFix f 'BooleanSort -> IFix f s -> IFix f s -> IFix f s
ite i t e = inject (IfThenElse (sing :: Sing s) i t e)
