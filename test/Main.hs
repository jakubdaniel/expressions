{-# LANGUAGE DataKinds
           , KindSignatures
           , OverloadedStrings
           , RankNTypes
           , TypeOperators #-}

import Data.Maybe
import Data.Singletons
import Data.Text
import Prelude hiding (and)
import Test.QuickCheck hiding ((.&.))
import Test.Tasty
import Test.Tasty.QuickCheck hiding ((.&.))

import Data.Expression

parseJust :: forall f (s :: Sort). ( Parseable f f, SingI s ) => Text -> IFix f s
parseJust = fromJust . parse

main :: IO ()
main = defaultMain $ testGroup "parsing" [ testProperty "1" $ once $ var "a" == (parseJust "(a : int)" :: ALia 'IntegralSort)
                                         , testProperty "2" $ once $ var "a" /= (parseJust "(+ (a : int) 3)" :: ALia 'IntegralSort)
                                         , testProperty "3" $ once $ var "a" .+. cnst 1 == (parseJust "(+ (a : int) 1)" :: ALia 'IntegralSort)
                                         , testProperty "4" $ once $ select (var "a") (var "b" .+. cnst 3) == (parseJust "(select (a : array int (array int bool)) (+ (b : int) 3))" :: QFALia ('ArraySort 'IntegralSort 'BooleanSort))
                                         , testProperty "5" $ once $ forall [var "x" :: Var 'IntegralSort] (exists [var "y" :: Var 'IntegralSort] (and [true, var "b" .=. (var "x" .<. var "y")])) == (parseJust "(forall ((x : int)) (exists ((y : int)) (and true (= (b : bool) (< x y)))))" :: Lia 'BooleanSort)
                                         , testProperty "6" $ once $ forall [var "x" :: Var 'IntegralSort, var "y"] (var "x" .<. var "y" .+. var "z") .&. var "z" .=. cnst 3 == (parseJust "(and (forall ((x : int) (y : int)) (< x (+ y (z : int)))) (= z 3))" :: Lia 'BooleanSort) ]
