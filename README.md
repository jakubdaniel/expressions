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

## distinguish quantifier-free from quantified formulae

    λ> isQuantified (var "z" .&. (exists [var "b" :: Var 'IntegralSort] (var "a" .+. var "b" .=. var "c" .+. var "d")) :: Lia 'BooleanSort)
    True

    λ> isQuantifierFree (var "z" .&. var "a" .+. var "b" .=. var "c" .+. var "d" :: Lia 'BooleanSort)
    True

## negation normal form

    λ> nnf (not (var "z" .&. (exists [var "b" :: Var 'IntegralSort] (var "a" .+. var "b" .=. var "c" .+. var "d")) :: Lia 'BooleanSort))
    (or (not (z : bool)) (forall ((b : int)) (not (= (+ (a : int) (b : int)) (+ (c : int) (d : int))))))

## prenex form

    λ> prenex (forall [var "a" :: Var 'IntegralSort] (var "b" .&. not (exists [var "c" :: Var 'BooleanSort] (var "c" .->. var "d")) .&. forall [var "d" :: Var 'IntegralSort] (var "d" .+. var "a" ./=. cnst 3)) :: Lia 'BooleanSort)
    (forall ((f2 : int) (f1 : int)) (forall ((f0 : bool)) (and (b : bool) (and (f0 : bool) (not (d : bool))) (not (= (+ (f1 : int) (f2 : int)) 3)))))

## flat form

    λ> flatten (select (var "a") (var "i" .+. cnst 1) .=. cnst 3 :: ALia 'BooleanSort)
    (exists ((k0 : int)) (and (= (k0 : int) (+ 1 (i : int))) (= (select (a : array int int) (k0 : int)) 3)))

    λ> type L = IFix (UniversalF ('ArraySort 'IntegralSort 'IntegralSort) :+: ALiaF)
    λ> flatten (select (store (var "a") (var "i") (cnst 3)) (cnst 4) .=. var "b" :: L 'BooleanSort)
    (forall ((k0 : array int int)) (or (not (= (k0 : array int int) (store (a : array int int) (i : int) 3))) (= (select (k0 : array int int) 4) (b : int))))

    λ> type L = IFix (UniversalF ('ArraySort 'IntegralSort 'IntegralSort) :+: ExistentialF ('ArraySort 'IntegralSort 'IntegralSort) :+: ALiaF)
    λ> flatten (select (store (var "a") (var "i") (cnst 3)) (cnst 4) .=. var "b" :: L 'BooleanSort)
    (exists ((k0 : array int int)) (and (= (k0 : array int int) (store (a : array int int) (i : int) 3)) (= (select (k0 : array int int) 4) (b : int))))

---

See [documentation](https://jakubdaniel.github.io/expressions/).
