[![Hackage](https://img.shields.io/hackage/v/expressions.svg)](https://hackage.haskell.org/package/expressions)
[![Hackage Deps](https://img.shields.io/hackage-deps/v/expressions.svg)](https://packdeps.haskellers.com/feed?needle=expressions)
[![Build Status](https://travis-ci.org/jakubdaniel/expressions.svg?branch=master)](https://travis-ci.org/jakubdaniel/expressions)

# expressions

    λ> :set -XDataKinds -XTypeOperators -XOverloadedStrings
    λ> import Data.Expression
    λ> import Data.Maybe

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

## equating expressions

    λ> var "a" == (fromJust $ parse "(a : int)" :: ALia 'IntegralSort)
    True

    λ> var "a" == (fromJust $ parse "(+ (a : int) 3)" :: ALia 'IntegralSort)
    False

    λ> var "a" .+. cnst 1 == (fromJust $ parse "(+ (a : int) 1)" :: ALia 'IntegralSort)
    True

## substituting

    λ> (var "a" .+. (var "a" .+. cnst 3) :: ALia 'IntegralSort) `substitute` (cnst 3 `for` (var "a" .+. cnst 3))
    (+ (a : int) 3)

## listing variables

    λ> vars (forall [var "a" :: Var 'IntegralSort] (exists [var "b" :: Var 'IntegralSort] (var "a" .+. var "b" .=. var "c" .+. var "d")) :: Lia 'BooleanSort)
    [(a : int),(b : int),(c : int),(d : int)]

    λ> freevars (forall [var "a" :: Var 'IntegralSort] (exists [var "b" :: Var 'IntegralSort] (var "a" .+. var "b" .=. var "c" .+. var "d")) :: Lia 'BooleanSort)
    [(c : int),(d : int)]

---

See [documentation](https://jakubdaniel.github.io/expressions/).
