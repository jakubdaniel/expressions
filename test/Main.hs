{-# LANGUAGE DataKinds
           , FlexibleContexts
           , KindSignatures
           , OverloadedStrings
           , RankNTypes
           , TypeOperators #-}

import Control.Monad
import Data.Maybe
import Data.Singletons
import Data.Text
import Prelude hiding (and)

import qualified Prelude as P

import Data.Expression

parseJust :: forall f (s :: Sort). ( Parseable f f, SingI s ) => Text -> IFix f s
parseJust = fromJust . parse

a, b, x, y, z :: forall f (s :: Sort). ( VarF :<: f, SingI s ) => IFix f s
a = var "a"
b = var "b"
x = var "x"
y = var "y"
z = var "z"

c1, c3 :: forall f. ArithmeticF :<: f => IFix f 'IntegralSort
c1 = cnst 1
c3 = cnst 3

main :: IO ()
main = guard (P.and props) where

    props = [ e1 == parseJust "(a : int)"
            , e2 /= parseJust "(+ (a : int) 3)"
            , e3 == parseJust "(+ (a : int) 1)"
            , e4 == parseJust "(select (a : array int (array int bool)) (+ (b : int) 3))"
            , e5 == parseJust "(forall ((x : int)) (exists ((y : int)) (and true (= (b : bool) (< x y)))))"
            , e6 == parseJust "(and (forall ((x : int) (y : int)) (< x (+ y (z : int)))) (= z 3))"
            , e7 == e8 ]

    e1, e2, e3 :: ALia 'IntegralSort
    e1 = a
    e2 = a
    e3 = a .+. c1

    e4 :: QFALia ('ArraySort 'IntegralSort 'BooleanSort)
    e4 = select a (b .+. c3)

    e5, e6 :: Lia 'BooleanSort
    e5 = forall [x :: Var 'IntegralSort] (exists [y :: Var 'IntegralSort] (and [true, b .=. (x .<. y)]))
    e6 = forall [x :: Var 'IntegralSort, y] (x .<. y .+. z) .&. z .=. c3

    e7, e8 :: Lia 'IntegralSort
    e7 = a .*. (a .+. c3) `substitute` (c3 `for` (a .+. c3))
    e8 = inject (Mul [a, c3])
