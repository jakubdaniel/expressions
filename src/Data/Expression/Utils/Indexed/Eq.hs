{-# LANGUAGE RankNTypes
           , TypeInType #-}

--------------------------------------------------------------------------------
-- |
-- Module     :  Data.Expression.Utils.Indexed.Eq
-- Copyright  :  (C) 2017-18 Jakub Daniel
-- License    :  BSD-style (see the file LICENSE)
-- Maintainer :  Jakub Daniel <jakub.daniel@protonmail.com>
-- Stability  :  experimental
--------------------------------------------------------------------------------

module Data.Expression.Utils.Indexed.Eq where

import Data.Kind

-- | Indexed types that can be equated
class IEq (a :: i -> *) where
    ieq :: forall j. a j -> a j -> Bool

-- | Type constructors (usually functors) that produce types that can be equated
class IEq1 (f :: (i -> *) -> (i -> *)) where
    ieq1 :: forall a j. IEq a => f a j -> f a j -> Bool
