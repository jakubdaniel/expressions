[![Hackage](https://img.shields.io/hackage/v/expressions.svg)](https://hackage.haskell.org/package/expressions)
[![Hackage Deps](https://img.shields.io/hackage-deps/v/expressions.svg)](https://packdeps.haskellers.com/feed?needle=expressions)
[![Build Status](https://travis-ci.org/jakubdaniel/expressions.svg?branch=master)](https://travis-ci.org/jakubdaniel/expressions)

# expressions

    λ> :set -XDataKinds -XTypeOperators -XOverloadedStrings
    λ> import Data.Expression

## defining expressions

    λ> var "a" .+. var "b" :: ALia 'IntegralSort
    (+ (a : int) (b : int))

    λ> select (var "a" :: ALia ('ArraySort 'IntegralSort 'IntegralSort)) (var "i") .+. var "b" :: ALia 'IntegralSort
    (+ (select (a : array int int) (i : int)) (b : int))

## parsing expressions

    λ> parse "(select (a : array int (array int bool)) (+ (b : int) 3))" :: Maybe (QFALia ('ArraySort 'IntegralSort 'BooleanSort))
    Just (select (a : array int (array int bool)) (+ (b : int) 3))

    λ> parse "(forall ((x : int)) (exists ((y : int)) (and true (= (b : bool) (< x y)))))" :: Maybe (Lia 'BooleanSort)
    Just (forall ((x : int)) (exists ((y : int)) (and true (= (b : bool) (< (x : int) (y : int))))))

    λ> parse "(and (forall ((x : int) (y : int)) (< x (+ y (z : int)))) (= z 3))" :: Maybe (Lia 'BooleanSort)
    Just (and (forall ((x : int) (y : int)) (< (x : int) (+ (y : int) (z : int)))) (= (z : int) 3))

---

See [documentation](https://jakubdaniel.github.io/expressions/).
