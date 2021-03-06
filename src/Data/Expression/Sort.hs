{-# OPTIONS_GHC -fno-warn-unused-binds #-}

{-# LANGUAGE DataKinds
           , EmptyCase
           , FlexibleInstances
           , GADTs
           , KindSignatures
           , OverloadedStrings
           , QuantifiedConstraints
           , RankNTypes
           , ScopedTypeVariables
           , TemplateHaskell
           , TypeFamilies
           , TypeOperators
           , TypeSynonymInstances
           , TypeInType
           , UndecidableInstances #-}

--------------------------------------------------------------------------------
-- |
-- Module     :  Data.Expression.Sort
-- Copyright  :  (C) 2017-18 Jakub Daniel
-- License    :  BSD-style (see the file LICENSE)
-- Maintainer :  Jakub Daniel <jakub.daniel@protonmail.com>
-- Stability  :  experimental
--------------------------------------------------------------------------------

module Data.Expression.Sort ( Sort(..)
                            , Sing(..)
                            , withSort
                            , DynamicSort(..)
                            , DynamicallySorted(..)
                            , DynamicallySortedFix
                            , parseSort
                            , toDynamicallySorted
                            , toStaticSort
                            , toStaticallySorted ) where

import Data.Attoparsec.Text
import Data.Functor
import Data.Singletons
import Data.Singletons.Decide
import Data.Singletons.TH

import Data.Expression.Utils.Indexed.Functor

-- | A universe of recognized sorts
data Sort = BooleanSort                                  -- ^ booleans (true, false)
          | IntegralSort                                 -- ^ integers (..., -1, 0, 1, ...)
          | ArraySort { index :: Sort, element :: Sort } -- ^ arrays indexed by `index` sort, containing elements of `element` sort
    deriving Eq

genSingletons [''Sort]
singDecideInstance ''Sort

-- | Turn implicit sort parameter into explicit one
withSort :: forall a (s :: Sort). Sing s -> (SingI s => a) -> a
withSort SBooleanSort     a = a
withSort SIntegralSort    a = a
withSort (SArraySort i e) a = withSort i $ withSort e $ a

show' :: Sort -> String
show' BooleanSort     = "bool"
show' IntegralSort    = "int"
show' (ArraySort i e) = "(array " ++ show' i ++ " " ++ show' e ++ ")"

instance Show Sort where
    show s@BooleanSort   = show' s
    show s@IntegralSort  = show' s
    show (ArraySort i e) = "array " ++ show' i ++ " " ++ show' e

ssortToSort :: forall s. SSort s -> Sort
ssortToSort SBooleanSort     = BooleanSort
ssortToSort SIntegralSort    = IntegralSort
ssortToSort (SArraySort i e) = ArraySort (ssortToSort i) (ssortToSort e)

instance Show (SSort s) where
    show = show . ssortToSort

-- | Some sort (obtained for example during parsing)
data DynamicSort where
    DynamicSort :: forall (s :: Sort). Sing s -> DynamicSort

instance Eq DynamicSort where
    DynamicSort a == DynamicSort b = case a %~ b of
        Proved Refl -> True
        Disproved _ -> False

-- | A value of some sort
data DynamicallySorted (d :: Sort -> *) where
  DynamicallySorted :: forall (s :: Sort) d. Sing s -> d s -> DynamicallySorted d

-- | An expression of some sort (obtained for example during parsing)
type DynamicallySortedFix f = DynamicallySorted (IFix f)

instance (forall (s :: Sort). Eq (d s)) => Eq (DynamicallySorted d) where
    DynamicallySorted sa a == DynamicallySorted sb b = case sa %~ sb of
        Proved Refl -> a == b
        Disproved _ -> False

instance (forall (s :: Sort). Show (d s)) => Show (DynamicallySorted d) where
    show (DynamicallySorted _ a) = show a

-- | Tries to convert some sort (`DynamicSort`) to a requested sort.
toStaticSort :: forall (s :: Sort). SingI s => DynamicSort -> Maybe (Sing s)
toStaticSort dx = case dx of
    DynamicSort x -> case x %~ (sing :: Sing s) of
        Proved Refl -> Just x
        Disproved _ -> Nothing

-- | Converts a statically sorted expression to a dynamically sorted one.
toDynamicallySorted :: forall d (s :: Sort). SingI s => d s -> DynamicallySorted d
toDynamicallySorted = DynamicallySorted (sing :: Sing s)

-- | Tries to convert an expression (`DynamicallySorted`) of some sort to an expression of requested sort.
-- Performs no conversions.
toStaticallySorted :: forall d (s :: Sort). SingI s => DynamicallySorted d -> Maybe (d s)
toStaticallySorted dx = case dx of
    DynamicallySorted s x -> case s %~ (sing :: Sing s) of
        Proved Refl -> Just x
        Disproved _ -> Nothing

-- | Parser that accepts sort definitions such as @bool@, @int@, @array int int@, @array int (array ...)@.
parseSort :: Parser DynamicSort
parseSort = choice [ bool, int, array ] <?> "Sort" where
        bool  = string "bool" $> DynamicSort SBooleanSort
        int   = string "int"  $> DynamicSort SIntegralSort
        array = array' <$> (string "array" *> space *> sort') <*> (space *> sort')

        sort' = choice [ bool, int, char '(' *> array <* char ')' ]

        array' :: DynamicSort -> DynamicSort -> DynamicSort
        array' (DynamicSort i) (DynamicSort e) = DynamicSort (SArraySort i e)
