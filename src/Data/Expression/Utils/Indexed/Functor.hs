{-# LANGUAGE RankNTypes
           , TypeInType
           , UndecidableInstances #-}

--------------------------------------------------------------------------------
-- |
-- Module     :  Data.Expression.Utils.Indexed.Functor
-- Copyright  :  (C) 2017-18 Jakub Daniel
-- License    :  BSD-style (see the file LICENSE)
-- Maintainer :  Jakub Daniel <jakub.daniel@protonmail.com>
-- Stability  :  experimental
--------------------------------------------------------------------------------

module Data.Expression.Utils.Indexed.Functor (IFix(..), IFunctor(..), icata) where

import Data.Functor.Const
import Data.Kind

import Data.Expression.Utils.Indexed.Eq
import Data.Expression.Utils.Indexed.Show

-- | A fixpoint of a functor in indexed category
newtype IFix f i = IFix { unIFix :: f (IFix f) i }

-- | A functor in indexed category
class IFunctor (f :: (i -> *) -> (i -> *)) where
    imap :: (forall i'. a i' -> b i') -> (forall i'. f a i' -> f b i')

-- | Indexed catamorphism
icata :: IFunctor f => (forall i. f a i -> a i) -> (forall i. IFix f i -> a i)
icata f = f . imap (icata f) . unIFix

instance IEq1 f => IEq (IFix f) where
    IFix a `ieq` IFix b = a `ieq1` b

instance IEq1 f => Eq (IFix f i) where
    IFix a == IFix b = a `ieq1` b

instance (IFunctor f, IShow f) => Show (IFix f i) where
    show = getConst . icata ishow
