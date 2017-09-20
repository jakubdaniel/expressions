{-# LANGUAGE FlexibleInstances
           , MultiParamTypeClasses
           , OverloadedStrings
           , ScopedTypeVariables
           , TypeInType
           , TypeOperators
           , UndecidableInstances #-}

--------------------------------------------------------------------------------
-- |
-- Module     :  Data.Expression.Parser
-- Copyright  :  (C) 2017-18 Jakub Daniel
-- License    :  BSD-style (see the file LICENSE)
-- Maintainer :  Jakub Daniel <jakub.daniel@protonmail.com>
-- Stability  :  experimental
--------------------------------------------------------------------------------

module Data.Expression.Parser ( Context
                              , Parser
                              , Parseable(..)
                              , parse
                              , parseWith

                              , char
                              , choice
                              , decimal
                              , digit
                              , letter
                              , many1
                              , sepBy1
                              , signed
                              , space
                              , string

                              , identifier

                              , (<?>)

                              , assertSort
                              , assumeSort ) where

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State.Lazy
import Data.Map
import Data.Proxy
import Data.Singletons
import Data.Text hiding ( empty )
import Prelude hiding ( lookup )

import Data.Expression.Sort
import Data.Expression.Utils.Indexed.Functor
import Data.Expression.Utils.Indexed.Sum

import qualified Data.Attoparsec.Text as A

-- | Parsing context assigning sorts to known variables
type Context = Map String DynamicSort

-- | Context-sensitive parser that remembers sorts of variables
type Parser  = ReaderT Context (StateT Context A.Parser)

-- | Expressions that can be parsed
class Parseable f g where
    parser :: Proxy f -> Parser (DynamicallySorted g) -> Parser (DynamicallySorted g)

-- | Tries to parse the entire input text and produce an expression in desired language and with desired sort.
parse :: forall f (s :: Sort). ( Parseable f f, SingI s ) => Text -> Maybe (IFix f s)
parse = parseWith empty

-- | Like `parse` but allows adding initial assumption about sorts of some variables.
parseWith :: forall f (s :: Sort). ( Parseable f f, SingI s ) => Context -> Text -> Maybe (IFix f s)
parseWith c = let a = parser (Proxy :: Proxy f) a in toStaticallySorted <=< A.maybeResult . flip A.feed "" . A.parse (evalStateT (runReaderT a c) empty <* A.endOfInput)

instance (Parseable f h, Parseable g h) => Parseable (f :+: g) h where
    parser _ r = A.choice [ parser (Proxy :: Proxy f) r, parser (Proxy :: Proxy g) r ]

-- | Matches a given character.
char :: Char -> Parser Char
char = lift . lift . A.char

-- | Matches first of many choices.
choice :: [Parser a] -> Parser a
choice = A.choice

-- | Matches a given decimal number.
decimal :: Parser Int
decimal = lift . lift $ A.decimal

-- | Matches a given digit.
digit :: Parser Char
digit = lift . lift $ A.digit

-- | Matches any character.
letter :: Parser Char
letter = lift . lift $ A.letter

-- | Matches one or more times.
many1 :: Parser a -> Parser [a]
many1 = A.many1

-- | Matches one or more times, separated by specified separator.
sepBy1 :: Parser a -> Parser s -> Parser [a]
sepBy1 = A.sepBy1

-- | Matches a signed number.
signed :: Parser Int -> Parser Int
signed m = (*) <$> (lift . lift) (A.signed (pure 1)) <*> m

-- | Matches space.
space :: Parser Char
space = lift . lift $ A.space

-- | Matches a given string.
string :: Text -> Parser Text
string = lift . lift . A.string

-- | Matches identifier that starts with [a-zA-Z'_@#] and is followed by [a-zA-Z'_@#0-9].
identifier :: Parser String
identifier = (:) <$> id' <*> A.many' (choice [ id', digit ]) where
    id' = choice [ letter, char '\'', char '_', char '@', char '#' ]

-- | Labels parser.
(<?>) :: Parser a -> String -> Parser a
a <?> l = ReaderT $ \r -> StateT $ \s -> runStateT (runReaderT a r) s A.<?> l

-- | Asserts what sort is assigned to a variable in current context.
assertSort :: String -> DynamicSort -> Parser ()
assertSort n s = do
    ss <- ask
    ds <- lift get

    case n `lookup` (ss `union` ds) of
        Just s' -> when (s /= s') $ fail "sort mismatch"
        Nothing -> lift $ modify (insert n s)

-- | Variable assumes sort based on current context.
assumeSort :: String -> Parser DynamicSort
assumeSort n = do
    ss <- ask
    ds <- lift get

    case n `lookup` (ss `union` ds) of
        Just s  -> return s
        Nothing -> fail "unspecified sort"
