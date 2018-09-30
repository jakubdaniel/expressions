{-# LANGUAGE KindSignatures
           , RankNTypes
           , TypeInType #-}

--------------------------------------------------------------------------------
-- |
-- Module     :  Data.Expression.Utils.Indexed.Traversable
-- Copyright  :  (C) 2017-18 Jakub Daniel
-- License    :  BSD-style (see the file LICENSE)
-- Maintainer :  Jakub Daniel <jakub.daniel@protonmail.com>
-- Stability  :  experimental
--------------------------------------------------------------------------------

module Data.Expression.Utils.Indexed.Traversable where

import Control.Monad

import Data.Expression.Utils.Indexed.Functor

-- | Type constructors (usually functors) that can be traversed
class ITraversable (t :: (i -> *) -> (i -> *))  where
    itraverse :: forall (a :: i -> *) (b :: i -> *) f. Applicative f => (forall (i' :: i). a i' -> f (b i')) -> (forall (i' :: i). t a i' -> f (t b i'))

-- | Maps a monadic action over a traversable functor.
imapM :: ( ITraversable f, Monad m ) => (forall (i' :: i). IFix f i' -> m (IFix f i')) -> (forall (i' :: i). IFix f i' -> m (IFix f i'))
imapM f = f . IFix <=< itraverse (imapM f) . unIFix
