{-# LANGUAGE TypeInType #-}

--------------------------------------------------------------------------------
-- |
-- Module     :  Data.Expression.Utils.Indexed.Show
-- Copyright  :  (C) 2017-18 Jakub Daniel
-- License    :  BSD-style (see the file LICENSE)
-- Maintainer :  Jakub Daniel <jakub.daniel@protonmail.com>
-- Stability  :  experimental
--------------------------------------------------------------------------------

module Data.Expression.Utils.Indexed.Show where

import Data.Functor.Const

-- | `Show` for indexed type constructors (most importantly functors)
class IShow f where
    ishow :: f (Const String) i -> Const String i
