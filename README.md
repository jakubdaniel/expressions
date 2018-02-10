[![Hackage](https://img.shields.io/hackage/v/expressions.svg)](https://hackage.haskell.org/package/expressions)
[![Hackage Deps](https://img.shields.io/hackage-deps/v/expressions.svg)](https://packdeps.haskellers.com/feed?needle=expressions)
[![Build Status](https://travis-ci.org/jakubdaniel/expressions.svg?branch=master)](https://travis-ci.org/jakubdaniel/expressions)

# expressions

    λ> :set -XDataKinds -XFlexibleContexts -XKindSignatures -XOverloadedStrings -XRankNTypes -XTypeOperators
    λ> import Data.Expression as E
    λ> import Data.Maybe
    λ> import Data.Singletons
    λ> import Data.Text

## defining expressions

    λ> var "a" .+. var "b" :: ALia 'IntegralSort
    (+ (a : int) (b : int))

    λ> :{
    let a, b, c, d, x, y, z, i :: forall f (s :: Sort). ( VarF :<: f, SingI s ) => IFix f s
        a = var "a"
        b = var "b"
        c = var "c"
        d = var "d"
        x = var "x"
        y = var "y"
        z = var "z"
        i = var "i"
    :}

    λ> select a (i :: ALia 'IntegralSort) .+. b :: ALia 'IntegralSort
    (+ (select (a : array int int) (i : int)) (b : int))

## parsing expressions

    λ> :{
    let in1, in2, in3 :: Text
        in1 = "(select (a : array int (array int bool)) (+ (b : int) 3))"
        in2 = "(forall ((x : int)) (exists ((y : int)) (and true (= (b : bool) (< x y)))))"
        in3 = "(and (forall ((x : int) (y : int)) (< x (+ y (z : int)))) (= z 3))"
    :}

    λ> parse in1 :: Maybe (QFALia ('ArraySort 'IntegralSort 'BooleanSort))
    Just (select (a : array int (array int bool)) (+ 3 (b : int)))

    λ> parse in2 :: Maybe (Lia 'BooleanSort)
    Just (forall ((x : int)) (exists ((y : int)) (= (b : bool) (< (x : int) (y : int)))))

    λ> parse in3 :: Maybe (Lia 'BooleanSort)
    Just (and (forall ((x : int) (y : int)) (< (x : int) (+ (y : int) (z : int)))) (= (z : int) 3))

## equating expressions

    λ> a == (fromJust $ parse "(a : int)" :: ALia 'IntegralSort)
    True

    λ> a == (fromJust $ parse "(+ (a : int) 3)" :: ALia 'IntegralSort)
    False

    λ> a .+. cnst 1 == (fromJust $ parse "(+ (a : int) 1)" :: ALia 'IntegralSort)
    True

## substituting

    λ> (a .*. (a .+. cnst 3) :: ALia 'IntegralSort) `substitute` (cnst 3 `for` (a .+. cnst 3))
    (* (a : int) 3)

## listing variables

    λ> :{
    let ai, bi :: Var 'IntegralSort
        ai = a
        bi = b
    
        qe :: Lia 'BooleanSort
        qe = forall [ai] (exists [bi] (a .+. b .=. c .+. d))
    :}

    λ> vars qe
    [(a : int),(b : int),(c : int),(d : int)]

    λ> freevars qe
    [(c : int),(d : int)]

## distinguish quantifier-free from quantified formulae

    λ> isQuantified (z .&. (exists [b :: Var 'IntegralSort] (a .+. b .=. c .+. d)) :: Lia 'BooleanSort)
    True

    λ> isQuantifierFree (z .&. a .+. b .=. c .+. d :: Lia 'BooleanSort)
    True

## negation normal form

    λ> nnf (E.not (z .&. (exists [b :: Var 'IntegralSort] (a .+. b .=. c .+. d)) :: Lia 'BooleanSort))
    (or (not (z : bool)) (forall ((b : int)) (not (= (+ (a : int) (b : int)) (+ (c : int) (d : int))))))

## prenex form

    λ> :{
    let cb :: Var 'BooleanSort
        cb = c
        di :: Var 'IntegralSort
        di = d
        qe :: Lia 'BooleanSort
        qe = forall [ai] (b .&. E.not (exists [cb] (c .->. d)) .&. forall [di] (d .+. a ./=. cnst 3))
    :}

    λ> prenex qe
    (forall
      ((f2 : int) (f1 : int))
      (forall
        ((f0 : bool))
        (and
          (b : bool)
          (and (f0 : bool) (not (d : bool)))
          (not (= (+ (f1 : int) (f2 : int)) 3))
        )
      )
    )

## flat form

    λ> flatten (select a (i .+. cnst 1) .=. cnst 3 :: ALia 'BooleanSort)
    (exists ((k0 : int)) (and (= (k0 : int) (+ 1 (i : int))) (= (select (a : array int int) (k0 : int)) 3)))

    λ> type L1 = UniversalF ('ArraySort 'IntegralSort 'IntegralSort) :+: ALiaF
    λ> flatten (select (store a i (cnst 3)) (cnst 4) .=. b :: IFix L1 'BooleanSort)
    (forall
      ((k0 : array int int))
      (or
        (not (= (k0 : array int int) (store (a : array int int) (i : int) 3)))
        (= (select (k0 : array int int) 4) (b : int))
      )
    )

    λ> type L2 = ExistentialF ('ArraySort 'IntegralSort 'IntegralSort) :+: L1
    λ> flatten (select (store a i (cnst 3)) (cnst 4) .=. b :: IFix L2 'BooleanSort)
    (exists
      ((k0 : array int int))
      (and
        (= (k0 : array int int) (store (a : array int int) (i : int) 3))
        (= (select (k0 : array int int) 4) (b : int))
      )
    )

## replace store terms using axiom

    λ> unstore (select (store a i (cnst 3)) (cnst 4) .=. b :: IFix L2 'BooleanSort)
    (exists
      ((k0 : array int int))
      (and
        (and
          (= (select (k0 : array int int) (i : int)) 3)
          (forall
            ((m0 : int))
              (or
                (= (i : int) (m0 : int))
                (= (select (k0 : array int int) (m0 : int)) (select (a : array int int) (m0 : int)))
              )
          )
        )
        (= (select (k0 : array int int) 4) (b : int))
      )
    )

---

See [documentation](https://jakubdaniel.github.io/expressions/).
