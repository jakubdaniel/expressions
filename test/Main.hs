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

    props = [ e1 == (parseJust "(a : int)"                                                                   :: ALia 'IntegralSort)
            , e2 /= (parseJust "(+ (a : int) 3)"                                                             :: ALia 'IntegralSort)
            , e3 == (parseJust "(+ (a : int) 1)"                                                             :: ALia 'IntegralSort)
            , e4 == (parseJust "(select (a : array int (array int bool)) (+ (b : int) 3))"                   :: QFALia ('ArraySort 'IntegralSort 'BooleanSort))
            , e5 == (parseJust "(forall ((x : int)) (exists ((y : int)) (and true (= (b : bool) (< x y)))))" :: Lia 'BooleanSort)
            , e6 == (parseJust "(and (forall ((x : int) (y : int)) (< x (+ y (z : int)))) (= z 3))"          :: Lia 'BooleanSort) ]

    e1 = a
    e2 = a
    e3 = a .+. c1
    e4 = select a (b .+. c3)
    e5 = forall [x :: Var 'IntegralSort] (exists [y :: Var 'IntegralSort] (and [true, b .=. (x .<. y)]))
    e6 = forall [x :: Var 'IntegralSort, y] (x .<. y .+. z) .&. z .=. c3
