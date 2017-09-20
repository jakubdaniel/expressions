{-# LANGUAGE RankNTypes
           , TypeInType #-}

--------------------------------------------------------------------------------
-- |
-- Module     :  Data.Expression.Utils.Indexed.Foldable
-- Copyright  :  (C) 2017-18 Jakub Daniel
-- License    :  BSD-style (see the file LICENSE)
-- Maintainer :  Jakub Daniel <jakub.daniel@protonmail.com>
-- Stability  :  experimental
--------------------------------------------------------------------------------

module Data.Expression.Utils.Indexed.Foldable (IFoldable(..)) where

import Data.Functor.Const
import Data.Kind

-- | Type constructors (usually functors) that can be folded
class IFoldable (f :: (i -> *) -> (i -> *)) where
    ifold :: Monoid m => f (Const m) i' -> Const m i'
