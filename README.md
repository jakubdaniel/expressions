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

---

See [documentation](https://jakubdaniel.github.io/expressions/).
