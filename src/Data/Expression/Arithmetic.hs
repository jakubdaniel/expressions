{-# LANGUAGE DataKinds
           , FlexibleContexts
           , GADTs
           , RankNTypes
           , ScopedTypeVariables
           , TypeInType
           , TypeOperators #-}

--------------------------------------------------------------------------------
-- |
-- Module     :  Data.Expression.Arithmetic
-- Copyright  :  (C) 2017-18 Jakub Daniel
-- License    :  BSD-style (see the file LICENSE)
-- Maintainer :  Jakub Daniel <jakub.daniel@protonmail.com>
-- Stability  :  experimental
--------------------------------------------------------------------------------

module Data.Expression.Arithmetic ( ArithmeticF(..)
                                  , cnst
                                  , add
                                  , mul
                                  , (.+.)
                                  , (.*.)
                                  , (.\.)
                                  , (.<.)
                                  , (.>.)
                                  , (.<=.)
                                  , (.>=.) ) where

import Data.List
import Data.Maybe
import Data.Monoid

import Data.Expression.Sort
import Data.Expression.Utils.Indexed.Functor
import Data.Expression.Utils.Indexed.Show
import Data.Expression.Utils.Indexed.Sum

import qualified Data.Functor.Const as F

-- | A functor representing linear integer arithmetic: constants (`cnst`), addition (`add` or `.+.`), multiplication (`mul` or `.*.`), divisibility predicate (`.\.`) and ordering (`.<.`, `.>.`, `.<=.`, `.>=.`).
data ArithmeticF a (s :: Sort) where
    Const    :: Int -> ArithmeticF a 'IntegralSort
    Add      :: [a 'IntegralSort] -> ArithmeticF a 'IntegralSort
    Mul      :: [a 'IntegralSort] -> ArithmeticF a 'IntegralSort
    Divides  :: Int -> a 'IntegralSort -> ArithmeticF a 'BooleanSort
    LessThan :: a 'IntegralSort -> a 'IntegralSort -> ArithmeticF a 'BooleanSort

instance IFunctor ArithmeticF where
    imap _ (Const c)        = Const c
    imap f (Add as)         = Add $ map f as
    imap f (Mul ms)         = Mul $ map f ms
    imap f (c `Divides`  a) = c `Divides` f a
    imap f (a `LessThan` b) = f a `LessThan` f b

instance IShow ArithmeticF where
    ishow (Const c)        = F.Const $ show c
    ishow (Add as)         = F.Const $ "(+ " ++ intercalate " " (map F.getConst as) ++ ")"
    ishow (Mul ms)         = F.Const $ "(* " ++ intercalate " " (map F.getConst ms) ++ ")"
    ishow (c `Divides`  a) = F.Const $ "(" ++ show c ++ "| " ++ F.getConst a ++ ")"
    ishow (a `LessThan` b) = F.Const $ "(< " ++ F.getConst a ++ " " ++ F.getConst b ++ ")"

-- | A smart constructor for integer constants
cnst :: ArithmeticF :<: f => Int -> IFix f 'IntegralSort
cnst = inject . Const

mergeConstAdd :: ArithmeticF :<: f => IFix f 'IntegralSort -> (Int, [IFix f 'IntegralSort]) -> (Int, [IFix f 'IntegralSort])
mergeConstAdd e (acc, r) = case match e of
    Just (Const c) -> (acc + c, r)
    _              -> (acc, e : r)

-- | A smart constructor for binary addition
(.+.) :: forall f. ArithmeticF :<: f => IFix f 'IntegralSort -> IFix f 'IntegralSort -> IFix f 'IntegralSort
a .+. b = merge . (\(c, r) -> if c == 0 then r else cnst c : r) . foldr mergeConstAdd (0, []) $ flatten a ++ flatten b where
    merge []  = cnst 0
    merge [e] = e
    merge es  = inject $ Add es

    flatten e = case match e of
        Just (Const 0) -> []
        Just (Add as)  -> as
        _              -> [e]

mergeConstMul :: ArithmeticF :<: f => IFix f 'IntegralSort -> (Int, [IFix f 'IntegralSort]) -> (Int, [IFix f 'IntegralSort])
mergeConstMul e (acc, r) = case match e of
    Just (Const c) -> (acc * c, r)
    _              -> (acc, e : r)

-- | A smart constructor for a binary multiplication
(.*.) :: forall f. ArithmeticF :<: f => IFix f 'IntegralSort -> IFix f 'IntegralSort -> IFix f 'IntegralSort
a .*. b = merge . (\(c, r) -> if c == 1 then r else cnst c : r) . foldr mergeConstMul (1, []) $ flatten a ++ flatten b where
    merge []  = cnst 1
    merge [e] = e
    merge es  = inject $ Mul es

    flatten e = case match e of
        Just (Const 1) -> []
        Just (Mul ms)  -> ms
        _              -> [e]

-- | A smart constructor for a variadic addition
add :: ArithmeticF :<: f => [IFix f 'IntegralSort] -> IFix f 'IntegralSort
add []  = cnst 0
add [a] = a
add as  = foldr (.+.) (cnst 0) as

-- | A smart constructor for a variadic multiplication
mul :: ArithmeticF :<: f => [IFix f 'IntegralSort] -> IFix f 'IntegralSort
mul []  = cnst 1
mul [m] = m
mul ms  = foldr (.*.) (cnst 1) ms

-- | A smart constructor for a divisibility predicate
(.\.) :: ArithmeticF :<: f => Int -> IFix f 'IntegralSort -> IFix f 'BooleanSort
c .\. a = inject $ c `Divides` a

(.<.), (.>.), (.<=.), (.>=.) :: forall f. ArithmeticF :<: f => IFix f 'IntegralSort -> IFix f 'IntegralSort -> IFix f 'BooleanSort

-- | A smart constructor for @<@
a .<. b = fromJust . getFirst $ First (mergeL a b) <> First (mergeR a b) <> First (Just . inject $ a `LessThan` b) where
    merge :: (IFix f 'IntegralSort -> IFix f 'IntegralSort -> IFix f 'BooleanSort) -> IFix f 'IntegralSort -> IFix f 'IntegralSort -> Maybe (IFix f 'BooleanSort)
    merge cmp c d = do
       (Const v) <- match c
       (Add as)  <- match d
       return . (\(v', r) -> cnst (-v') `cmp` add r) . foldr mergeConstAdd (0, []) $ cnst (-v) : as

    mergeL c d = merge (\x y -> inject $ x `LessThan` y) c d
    mergeR d c = merge (\x y -> inject $ y `LessThan` x) d c

-- | A smart constructor for @>@
a .>.  b = b .<. a

-- | A smart constructor for @<=@
a .<=. b = a .<. b .+. cnst 1

-- | A smart constructor for @>=@
a .>=. b = a .+. cnst 1 .>. b

infixl 9 .*.
infixl 8 .+.
infix  7 .\.
infix  7 .<.
infix  7 .>.
infix  7 .<=.
infix  7 .>=.
