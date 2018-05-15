{-# OPTIONS_GHC -fno-warn-unused-binds #-}

{-# LANGUAGE EmptyCase
           , DataKinds
           , GADTs
           , KindSignatures
           , OverloadedStrings
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
                            , DynamicSort(..)
                            , DynamicallySorted(..)
                            , parseSort
                            , toStaticSort
                            , toStaticallySorted ) where

import Data.Attoparsec.Text
import Data.Kind
import Data.Singletons
import Data.Singletons.Decide
import Data.Singletons.TH

import Data.Expression.Utils.Indexed.Eq
import Data.Expression.Utils.Indexed.Functor
import Data.Expression.Utils.Indexed.Show

-- | A universe of recognized sorts
data Sort = BooleanSort                                  -- ^ booleans (true, false)
          | IntegralSort                                 -- ^ integers (..., -1, 0, 1, ...)
          | ArraySort { index :: Sort, element :: Sort } -- ^ arrays indexed by `index` sort, containing elements of `element` sort
    deriving Eq

genSingletons [''Sort]
singDecideInstance ''Sort

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

-- | An expression of some sort (obtained for example during parsing)
data DynamicallySorted (f :: (Sort -> *) -> (Sort -> *)) where
  DynamicallySorted :: forall (s :: Sort) f. Sing s -> IFix f s -> DynamicallySorted f

instance IEq1 f => Eq (DynamicallySorted f) where
    DynamicallySorted sa a == DynamicallySorted sb b = case sa %~ sb of
        Proved Refl -> a == b
        Disproved _ -> False

instance (IFunctor f, IShow f) => Show (DynamicallySorted f) where
    show (DynamicallySorted _ a) = show a

-- | Tries to convert some sort (`DynamicSort`) to a requested sort.
toStaticSort :: forall (s :: Sort). SingI s => DynamicSort -> Maybe (Sing s)
toStaticSort dx = case dx of
    DynamicSort x -> case x %~ (sing :: Sing s) of
        Proved Refl -> Just x
        Disproved _ -> Nothing

-- | Tries to convert an expression (`DynamicallySorted`) of some sort to an expression of requested sort.
-- Performs no conversions.
toStaticallySorted :: forall f (s :: Sort). SingI s => DynamicallySorted f -> Maybe (IFix f s)
toStaticallySorted dx = case dx of
    DynamicallySorted s x -> case s %~ (sing :: Sing s) of
        Proved Refl -> Just x
        Disproved _ -> Nothing

-- | Parser that accepts sort definitions such as @bool@, @int@, @array int int@, @array int (array ...)@.
parseSort :: Parser DynamicSort
parseSort = choice [ bool, int, array ] <?> "Sort" where
        bool  = string "bool" *> pure (DynamicSort SBooleanSort)
        int   = string "int"  *> pure (DynamicSort SIntegralSort)
        array = array' <$> (string "array" *> space *> sort') <*> (space *> sort')

        sort' = choice [ bool, int, char '(' *> array <* char ')' ]

        array' :: DynamicSort -> DynamicSort -> DynamicSort
        array' (DynamicSort i) (DynamicSort e) = DynamicSort (SArraySort i e)
