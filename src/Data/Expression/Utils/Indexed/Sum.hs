{-# LANGUAGE FlexibleInstances
           , MultiParamTypeClasses
           , RankNTypes
           , TypeInType
           , TypeOperators #-}

--------------------------------------------------------------------------------
-- |
-- Module     :  Data.Expression.Utils.Indexed.Sum
-- Copyright  :  (C) 2017-18 Jakub Daniel
-- License    :  BSD-style (see the file LICENSE)
-- Maintainer :  Jakub Daniel <jakub.daniel@protonmail.com>
-- Stability  :  experimental
--------------------------------------------------------------------------------

module Data.Expression.Utils.Indexed.Sum ((:+:)(..), (:<:)(..), inject, match) where

import Data.Expression.Utils.Indexed.Functor
import Data.Expression.Utils.Indexed.Show

-- | Sum of two indexed functors
data (f :+: g) a i = InL (f a i) | InR (g a i)

infixr 8 :+:

instance (IFunctor f, IFunctor g) => IFunctor (f :+: g) where
    imap f (InL fa) = InL $ imap f fa
    imap f (InR ga) = InR $ imap f ga

-- | Inclusion relation for indexed sum functors
class (IFunctor f, IFunctor g) => f :<: g where
    inj :: f a i -> g a i
    prj :: g a i -> Maybe (f a i)

instance IFunctor f => f :<: f where
    inj = id
    prj = Just
instance (IFunctor f, IFunctor g) => f :<: (f :+: g) where
    inj = InL
    prj (InL a) = Just a
    prj (InR _) = Nothing
instance {-# OVERLAPPABLE #-} (IFunctor f, IFunctor g, IFunctor h, f :<: g) => f :<: (h :+: g) where
    inj = InR . inj
    prj (InL _) = Nothing
    prj (InR a) = prj a

-- | Inject a component into a sum.
inject :: g :<: f => forall i. g (IFix f) i -> IFix f i
inject = IFix . inj

-- | Try to unpack a sum into a component.
match :: g :<: f => forall i. IFix f i -> Maybe (g (IFix f) i)
match = prj . unIFix

instance (IShow f, IShow g) => IShow (f :+: g) where
    ishow (InL fa) = ishow fa
    ishow (InR ga) = ishow ga
