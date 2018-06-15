{-# LANGUAGE DataKinds
           , FlexibleContexts
           , FlexibleInstances
           , GADTs
           , MultiParamTypeClasses
           , OverloadedStrings
           , RankNTypes
           , ScopedTypeVariables
           , TypeInType
           , TypeOperators
           , UndecidableInstances #-}

--------------------------------------------------------------------------------
-- |
-- Module     :  Data.Expression
-- Copyright  :  (C) 2017-18 Jakub Daniel
-- License    :  BSD-style (see the file LICENSE)
-- Maintainer :  Jakub Daniel <jakub.daniel@protonmail.com>
-- Stability  :  experimental
--
-- Usage:
--
-- You can build expressions in predefined languages (`QFLogic`, `QFLia`,
-- `QFALia`, `Lia`, `ALia`) using the smart constructors such as `var`, `and`,
-- `or`, `not`, `forall`, `exists` (or operators `.&.`, `.|.`, `.->.`, `.<-.`,
-- `.<->.`) or you can define your own sorted language as a fixpoint (`IFix`)
-- of a sum (`:+:`) of indexed functors (`IFunctor`).
--------------------------------------------------------------------------------

module Data.Expression ( module Data.Expression.Arithmetic
                       , module Data.Expression.Array
                       , module Data.Expression.Equality
                       , module Data.Expression.IfThenElse
                       , module Data.Expression.Parser
                       , module Data.Expression.Sort
                       , module Data.Expression.Utils.Indexed.Eq
                       , module Data.Expression.Utils.Indexed.Foldable
                       , module Data.Expression.Utils.Indexed.Functor
                       , module Data.Expression.Utils.Indexed.Show
                       , module Data.Expression.Utils.Indexed.Sum
                       , module Data.Expression.Utils.Indexed.Traversable

                       -- Functors representing usual combinations of languages
                       , QFLogicF
                       , QFLiaF
                       , LiaF
                       , QFALiaF
                       , ALiaF

                       -- Simplest language
                       , Var

                       -- Usual languages
                       , QFLogic
                       , QFLia
                       , Lia
                       , QFALia
                       , ALia

                       -- Algebraic view of languages
                       , ComplementedLattice(..)

                       -- Convenient type synonyms
                       , VariableName

                       -- Functors representing the main language ingredients
                       , VarF(..)
                       , ConjunctionF(..)
                       , DisjunctionF(..)
                       , NegationF(..)
                       , UniversalF(..)
                       , ExistentialF(..)

                       -- Substitution facilities
                       , Substitution(..)
                       , substitute
                       , for

                       -- Smart expression constructors
                       , var
                       , true
                       , false
                       , and
                       , or
                       , not
                       , forall
                       , exists

                       -- Smart binary expression operators
                       , (.&.)
                       , (.|.)
                       , (.->.)
                       , (.<-.)
                       , (.<->.)
                       , (./=.)

                       -- Convenient destructors
                       , literals
                       , conjuncts
                       , disjuncts
                       , vars
                       , freevars

                       -- Predicates
                       , MaybeQuantified
                       , isQuantified
                       , isQuantifierFree

                       -- Special forms
                       , NNF
                       , nnf

                       , Prenex
                       , prenex

                       , Flatten
                       , flatten

                       , Unstore
                       , unstore ) where

import Algebra.Lattice
import Control.Applicative hiding (Const)
import Control.Comonad.Trans.Coiter
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State
import Data.Functor.Identity
import Data.List hiding (and, or, union)
import Data.Map hiding (map, drop, foldl, foldr, mapMaybe, partition)
import Data.Maybe
import Data.Monoid hiding ((<>))
import Data.Semigroup hiding (First, getFirst)
import Data.Singletons
import Data.Singletons.Decide
import Prelude hiding (and, or, not)

import Data.Expression.Arithmetic
import Data.Expression.Array
import Data.Expression.Equality
import Data.Expression.IfThenElse
import Data.Expression.Parser
import Data.Expression.Sort hiding (index)
import Data.Expression.Utils.Indexed.Eq
import Data.Expression.Utils.Indexed.Foldable
import Data.Expression.Utils.Indexed.Functor
import Data.Expression.Utils.Indexed.Show
import Data.Expression.Utils.Indexed.Sum
import Data.Expression.Utils.Indexed.Traversable

import qualified Data.Functor.Const as F
import qualified Prelude as P

-- | A functor representing propositional logic embedded in first order logic (quantifier-free, boolean variables aka propositions, logical connectives `and`, `or`, `not`, equality of propositions)
type QFLogicF = EqualityF :+: ConjunctionF :+: DisjunctionF :+: NegationF :+: VarF

-- | A functor representing the language of quantifier-free linear integer arithmetic theory in first order logic (integer constants, integer variables, addition, multiplication, divisibility, ordering)
type QFLiaF = ArithmeticF :+: IfThenElseF :+: QFLogicF

-- | A functor much like `QFLiaF` with quantifiers over booleans and integers
type LiaF = ExistentialF 'BooleanSort :+: ExistentialF 'IntegralSort :+: UniversalF 'BooleanSort :+: UniversalF 'IntegralSort :+: QFLiaF

-- | A functor representing the language of quantifier-free linear integer arithmetic and array theories in first order logic (much like `QFLiaF` with additional array variables, `select`, and `store`)
type QFALiaF = ArrayF :+: QFLiaF

-- | A functor much like `QFALiaF` with quantifiers over booleans and integers
type ALiaF = ExistentialF 'BooleanSort :+: ExistentialF 'IntegralSort :+: UniversalF 'BooleanSort :+: UniversalF 'IntegralSort :+: QFALiaF

-- | A language consisting solely of variables (useful for listing variables outside of any particular context, such as bound variables of quantified formula)
type Var = IFix VarF

-- | A language obtained as fixpoint of `QFLogicF`
type QFLogic = IFix QFLogicF

-- | A language obtained as fixpoint of `QFLiaF`
type QFLia   = IFix QFLiaF

-- | A language obtained as fixpoint of `LiaF`
type   Lia   = IFix   LiaF

-- | A language obtained as fixpoint of `QFALiaF`
type QFALia  = IFix QFALiaF

-- | A language obtained as fixpoint of `ALiaF`
type   ALia  = IFix   ALiaF

-- | Bounded lattices that support complementing elements
--
-- prop> complement . complement = id
-- 
class BoundedLattice a => ComplementedLattice a where
    complement :: a -> a

instance JoinSemiLattice (QFLogic 'BooleanSort) where a `join` b = a .|. b
instance JoinSemiLattice (QFLia   'BooleanSort) where a `join` b = a .|. b
instance JoinSemiLattice (  Lia   'BooleanSort) where a `join` b = a .|. b
instance JoinSemiLattice (QFALia  'BooleanSort) where a `join` b = a .|. b
instance JoinSemiLattice (  ALia  'BooleanSort) where a `join` b = a .|. b

instance MeetSemiLattice (QFLogic 'BooleanSort) where a `meet` b = a .&. b
instance MeetSemiLattice (QFLia   'BooleanSort) where a `meet` b = a .&. b
instance MeetSemiLattice (  Lia   'BooleanSort) where a `meet` b = a .&. b
instance MeetSemiLattice (QFALia  'BooleanSort) where a `meet` b = a .&. b
instance MeetSemiLattice (  ALia  'BooleanSort) where a `meet` b = a .&. b

instance Lattice (QFLogic 'BooleanSort)
instance Lattice (QFLia   'BooleanSort)
instance Lattice (  Lia   'BooleanSort)
instance Lattice (QFALia  'BooleanSort)
instance Lattice (  ALia  'BooleanSort)

instance BoundedJoinSemiLattice (QFLogic 'BooleanSort) where bottom = false
instance BoundedJoinSemiLattice (QFLia   'BooleanSort) where bottom = false
instance BoundedJoinSemiLattice (  Lia   'BooleanSort) where bottom = false
instance BoundedJoinSemiLattice (QFALia  'BooleanSort) where bottom = false
instance BoundedJoinSemiLattice (  ALia  'BooleanSort) where bottom = false

instance BoundedMeetSemiLattice (QFLogic 'BooleanSort) where top = true
instance BoundedMeetSemiLattice (QFLia   'BooleanSort) where top = true
instance BoundedMeetSemiLattice (  Lia   'BooleanSort) where top = true
instance BoundedMeetSemiLattice (QFALia  'BooleanSort) where top = true
instance BoundedMeetSemiLattice (  ALia  'BooleanSort) where top = true

instance BoundedLattice (QFLogic 'BooleanSort)
instance BoundedLattice (QFLia   'BooleanSort)
instance BoundedLattice (  Lia   'BooleanSort)
instance BoundedLattice (QFALia  'BooleanSort)
instance BoundedLattice (  ALia  'BooleanSort)

instance ComplementedLattice (QFLogic 'BooleanSort) where complement = nnf . not
instance ComplementedLattice (QFLia   'BooleanSort) where complement = nnf . not
instance ComplementedLattice (  Lia   'BooleanSort) where complement = nnf . not
instance ComplementedLattice (QFALia  'BooleanSort) where complement = nnf . not
instance ComplementedLattice (  ALia  'BooleanSort) where complement = nnf . not

-- | Type of names assigned to variables
type VariableName = String

-- | A functor representing a sorted variable, each variable is identified by its name and sort
data VarF a (s :: Sort) where
    Var :: VariableName -> Sing s -> VarF a s

instance IEq1 VarF where
    Var na _ `ieq1` Var nb _ = na == nb

instance IFunctor VarF where
    imap _ (Var n s) = Var n s
    index (Var _ s)  = s

instance IFoldable VarF where
    ifold _ = F.Const mempty

instance ITraversable VarF where
    itraverse _ (Var n s) = pure (Var n s)

instance IShow VarF where
    ishow (Var n s) = F.Const ("(" ++ n ++ " : " ++ show s ++ ")")

instance VarF :<: f => Parseable VarF f where
    parser _ _ = choice [ var', var'' ] <?> "Var" where
        var' = do
            _ <- char '('
            n <- identifier
            _ <- space *> char ':' *> space
            s <- lift . lift $ parseSort
            _ <- char ')'

            assertSort n s

            var''' n s

        var'' = do
            n <- many1 letter

            s <- assumeSort n

            var''' n s

        var''' :: VariableName -> DynamicSort -> Parser (DynamicallySorted f)
        var''' n (DynamicSort (s :: Sing s)) = return $ DynamicallySorted s (inject (Var n s))

-- | A smart constructor for variables of any sort in any language
-- Takes the variable name and infers the target language and sort from context.
--
-- @
-- var "a" :: Lia 'IntegralSort
-- @
var :: forall f s. ( VarF :<: f, SingI s ) => VariableName -> IFix f s
var n = inject (Var n (sing :: Sing s))

-- | Collects a list of all variables occurring in an expression (bound or free).
vars :: ( VarF :<: f, IFoldable f, IFunctor f ) => IFix f s -> [DynamicallySorted VarF]
vars = nub . F.getConst . icata vars' where
    vars' a = case prj a of
        Just (Var n s) -> F.Const [DynamicallySorted s . inject $ Var n s]
        Nothing -> ifold a

-- | Substitution that given an expression produces replacement if the expression is to be replaced or nothing otherwise.
newtype Substitution f = Substitution { runSubstitution :: forall (s :: Sort). IFix f s -> Maybe (IFix f s) }

-- | A simple constructor of substitutions that replaces the latter expression with the former.
for :: forall f (s :: Sort). ( IFunctor f, IEq1 f ) => IFix f s -> IFix f s -> Substitution f
b `for` a = Substitution $ \c -> case index (unIFix a) %~ index (unIFix c) of
    Proved Refl -> if a == c then Just b else Nothing
    Disproved _ -> Nothing

-- | Executes a substitution.
substitute :: ( IFunctor f, IEq1 f ) => IFix f s -> Substitution f -> IFix f s
substitute a s = case runSubstitution s a of
    Just b -> b
    Nothing -> IFix . imap (flip substitute s) . unIFix $ a

instance Semigroup (Substitution f) where
    (Substitution f) <> (Substitution g) = Substitution $ \a -> getFirst (mconcat ([First . f, First . g] <*> [a]))

instance Monoid (Substitution f) where
    mempty  = Substitution (const Nothing)
    mappend = (<>)

-- | A functor representing a logical connective for conjunction
data ConjunctionF a (s :: Sort) where
    And :: [a 'BooleanSort] -> ConjunctionF a 'BooleanSort

-- | A functor representing a logical connective for disjunction
data DisjunctionF a (s :: Sort) where
    Or  :: [a 'BooleanSort] -> DisjunctionF a 'BooleanSort

-- | A functor representing a logical connective for negation
data NegationF a (s :: Sort) where
    Not ::  a 'BooleanSort  -> NegationF a 'BooleanSort

instance IEq1 ConjunctionF where
    And as `ieq1` And bs = foldr (&&) True $ zipWith ieq as bs

instance IEq1 DisjunctionF where
    Or  as `ieq1` Or  bs = foldr (&&) True $ zipWith ieq as bs

instance IEq1 NegationF where
    Not a  `ieq1` Not b  = a `ieq` b

instance IFunctor ConjunctionF where
    imap f (And as) = And $ map f as
    index And {} = SBooleanSort

instance IFunctor DisjunctionF where
    imap f (Or os) = Or  $ map f os
    index Or {} = SBooleanSort

instance IFunctor NegationF where
    imap f (Not n)  = Not $ f n
    index Not {} = SBooleanSort

instance IFoldable ConjunctionF where
    ifold (And as) = F.Const . mconcat . map F.getConst $ as

instance IFoldable DisjunctionF where
    ifold (Or os) = F.Const . mconcat . map F.getConst $ os

instance IFoldable NegationF where
    ifold (Not n) = n

instance ITraversable ConjunctionF where
    itraverse f (And as) = And <$> traverse f as

instance ITraversable DisjunctionF where
    itraverse f (Or os) = Or <$> traverse f os

instance ITraversable NegationF where
    itraverse f (Not n) = Not <$> f n

instance IShow ConjunctionF where
    ishow (And []) = F.Const $ "true"
    ishow (And as) = F.Const $ "(and " ++ intercalate " " (map F.getConst as) ++ ")"

instance IShow DisjunctionF where
    ishow (Or []) = F.Const $ "false"
    ishow (Or os) = F.Const $ "(or "  ++ intercalate " " (map F.getConst os) ++ ")"

instance IShow NegationF where
    ishow (Not n)  = F.Const $ "(not " ++ F.getConst n ++ ")"

instance ConjunctionF :<: f => Parseable ConjunctionF f where
    parser _ r = choice [ true',  and' ] <?> "Conjunction" where
        true'  = string "true"  *> pure (toDynamicallySorted true)

        and' = do
            _  <- char '(' *> string "and" *> space
            as <- r `sepBy1` space
            _  <- char ')'
            and'' as

        and'' as = case mapM toStaticallySorted as of
            Just as' -> return . toDynamicallySorted . and $ as'
            Nothing  -> fail "and of non-boolean arguments"

instance DisjunctionF :<: f => Parseable DisjunctionF f where
    parser _ r = choice [ false', or' ] <?> "Disjunction" where
        false' = string "false" *> pure (toDynamicallySorted false)

        or' = do
            _  <- char '(' *> string "or" *> space
            os <- r `sepBy1` space
            _  <- char ')'
            or'' os

        or'' os = case mapM toStaticallySorted os of
            Just os' -> return . toDynamicallySorted . or $ os'
            Nothing  -> fail "or of non-boolean arguments"

instance NegationF :<: f => Parseable NegationF f where
    parser _ r = not' <?> "Negation" where
        not' = do
            _ <- char '(' *> string "not" *> space
            n <- r
            _ <- char ')'
            not'' n

        not'' n = case toStaticallySorted n of
            Just n' -> return . toDynamicallySorted . not $ n'
            Nothing -> fail "not of non-boolean arguments"

-- | `literals` decomposes a boolean combination (formed with conjunctions and disjunctions, preferably in negation normal form) into its constituents.
literals :: ( ConjunctionF :<: f, DisjunctionF :<: f ) => IFix f 'BooleanSort -> [IFix f 'BooleanSort]
literals e = fromMaybe [e]  $  (concatMap literals <$> conjuncts' e)
                           <|> (concatMap literals <$> disjuncts' e)

conjuncts' :: ConjunctionF :<: f => IFix f 'BooleanSort -> Maybe [IFix f 'BooleanSort]
conjuncts' e = (\(And as) -> as) <$> match e

disjuncts' :: DisjunctionF :<: f => IFix f 'BooleanSort -> Maybe [IFix f 'BooleanSort]
disjuncts' e = (\(Or  os) -> os) <$> match e

-- | `conjuncts` decomposes a conjunction into conjuncts.
conjuncts :: ConjunctionF :<: f => IFix f 'BooleanSort -> [IFix f 'BooleanSort]
conjuncts  e = fromMaybe [e] (conjuncts' e)

-- | `disjuncts` decomposes a disjunction into disjuncts.
disjuncts :: DisjunctionF :<: f => IFix f 'BooleanSort -> [IFix f 'BooleanSort]
disjuncts  e = fromMaybe [e] (disjuncts' e)

-- | A smart constructor for binary conjunction
(.&.) :: ConjunctionF :<: f => IFix f 'BooleanSort -> IFix f 'BooleanSort -> IFix f 'BooleanSort
a .&. b = merge (flatten'' a ++ flatten'' b) where
    merge []  = true
    merge [f] = f
    merge as  = inject $ And as

    flatten'' e = case match e of
        Just (And as) -> as
        _ -> [e]

-- | A smart constructor for binary disjunction
(.|.) :: DisjunctionF :<: f => IFix f 'BooleanSort -> IFix f 'BooleanSort -> IFix f 'BooleanSort
a .|. b = merge (flatten'' a ++ flatten'' b) where
    merge []  = false
    merge [f] = f
    merge os  = inject $ Or os

    flatten'' e = case match e of
        Just (Or os) -> os
        _ -> [e]

(.->.), (.<-.) :: ( DisjunctionF :<: f, NegationF :<: f ) => IFix f 'BooleanSort -> IFix f 'BooleanSort -> IFix f 'BooleanSort

-- | A smart constructor for implication (an abbreviation for @not a .|. b@)
a .->. b = not a .|. b

-- | A smart constructor for reversed implication (an abbreviation for @a .|. not b@)
a .<-. b = b .->. a

-- | A smart constructor for if-and-only-if connective
(.<->.) :: ( ConjunctionF :<: f, DisjunctionF :<: f, NegationF :<: f ) => IFix f 'BooleanSort -> IFix f 'BooleanSort -> IFix f 'BooleanSort
a .<->. b = (a .->. b) .&. (a .<-. b)

-- | A smart constructor for disequality
(./=.) :: forall f s. ( NegationF :<: f, EqualityF :<: f, SingI s ) => IFix f s -> IFix f s -> IFix f 'BooleanSort
a ./=. b = not (a .=. b)

infix  7 ./=.
infixr 6 .&.
infixr 5 .|.
infixr 4 .->.
infixl 4 .<-.
infix  3 .<->.

-- | Logical tautology
true :: ConjunctionF :<: f => IFix f 'BooleanSort
true = inject $ And []

-- | Logical contradiction
false :: DisjunctionF :<: f => IFix f 'BooleanSort
false = inject $ Or []

-- | A smart constructor for variadic conjunction
and :: ConjunctionF :<: f => [IFix f 'BooleanSort] -> IFix f 'BooleanSort
and []  = true
and [a] = a
and as  = foldr (.&.) true as

-- | A smart constructor for variadic disjunction
or :: DisjunctionF :<: f => [IFix f 'BooleanSort] -> IFix f 'BooleanSort
or []  = false
or [o] = o
or os  = foldr (.|.) false os

-- | A smart constructor for negation
not :: NegationF :<: f => IFix f 'BooleanSort -> IFix f 'BooleanSort
not n = case match n of
    Just (Not n') -> n'
    _ -> inject $ Not n

-- | A functor representing a mono-sorted universal quantifier binding a number of variables within a formula
data UniversalF (v :: Sort) a (s :: Sort) where
    Forall :: [Var v] -> a 'BooleanSort -> UniversalF v a 'BooleanSort

-- | A functor representing a mono-sorted existential quantifier binding a number of variables within a formula
data ExistentialF (v :: Sort) a (s :: Sort) where
    Exists :: [Var v] -> a 'BooleanSort -> ExistentialF v a 'BooleanSort

instance IEq1 (UniversalF v) where
    Forall as phi `ieq1` Forall bs psi = (foldr (&&) True $ zipWith ieq as bs) && phi `ieq` psi

instance IEq1 (ExistentialF v) where
    Exists as phi `ieq1` Exists bs psi = (foldr (&&) True $ zipWith ieq as bs) && phi `ieq` psi

instance IFunctor (UniversalF v) where
    imap f (Forall vs phi) = Forall vs $ f phi
    index Forall {} = SBooleanSort

instance IFunctor (ExistentialF v) where
    imap f (Exists vs phi) = Exists vs $ f phi
    index Exists {} = SBooleanSort

instance IFoldable (UniversalF v) where
    ifold (Forall _ b) = b

instance IFoldable (ExistentialF v) where
    ifold (Exists _ b) = b

instance ITraversable (UniversalF v) where
    itraverse f (Forall vs b) = Forall vs <$> f b

instance ITraversable (ExistentialF v) where
    itraverse f (Exists vs b) = Exists vs <$> f b

instance IShow (UniversalF v) where
    ishow (Forall vs phi) = F.Const $ "(forall (" ++ intercalate " " (map show vs) ++ ") " ++ F.getConst phi ++ ")"

instance IShow (ExistentialF v) where
    ishow (Exists vs phi) = F.Const $ "(exists (" ++ intercalate " " (map show vs) ++ ") " ++ F.getConst phi ++ ")"

instance ( UniversalF v :<: f, SingI v ) => Parseable (UniversalF v) f where
    parser _ r = forall' <?> "Universal" where
        var' :: Parser (DynamicallySorted VarF)
        var' = parser (Proxy :: Proxy VarF) var'

        forall' = do
            _   <- char '(' *> string "forall" *> space *> char '('
            vs  <- var' `sepBy1` space
            _   <- char ')' *> space
            phi <- local (union (fromList $ map context vs)) r
            _   <- char ')'
            forall'' vs phi

        forall'' [] _   = fail "quantifying zero variables"
        forall'' vs phi = case (mapM toStaticallySorted vs :: Maybe [Var v]) of
            Just vs' -> case toStaticallySorted phi of
                Just phi' -> return . toDynamicallySorted . forall vs' $ phi'
                Nothing   -> fail "quantifying non-boolean expression"
            Nothing  -> fail "ill-sorted quantifier"

        context (DynamicallySorted s v) = case match v of
            Just (Var n _) -> (n, DynamicSort s)
            _              -> error "impossible error"

instance ( ExistentialF v :<: f, SingI v ) => Parseable (ExistentialF v) f where
    parser _ r = exists' <?> "Existential" where
        var' :: Parser (DynamicallySorted VarF)
        var' = parser (Proxy :: Proxy VarF) var'

        exists' = do
            _   <- char '(' *> string "exists" *> space *> char '('
            vs  <- var' `sepBy1` space
            _   <- char ')' *> space
            phi <- local (union (fromList $ map context vs)) r
            _   <- char ')'
            exists'' vs phi

        exists'' [] _   = fail "quantifying zero variables"
        exists'' vs phi = case (mapM toStaticallySorted vs :: Maybe [Var v]) of
            Just vs' -> case toStaticallySorted phi of
                Just phi' -> return . toDynamicallySorted . exists vs' $ phi'
                Nothing   -> fail "quantifying non-boolean expression"
            Nothing  -> fail "ill-sorted quantifier"

        context (DynamicallySorted s v) = case match v of
            Just (Var n _) -> (n, DynamicSort s)
            _              -> error "impossible error"

class MaybeQuantified f where
    isQuantified' :: MaybeQuantified g => f (IFix g) s -> F.Const Any s
    freevars' :: f (F.Const [DynamicallySorted VarF]) s -> F.Const [DynamicallySorted VarF] s

instance MaybeQuantified VarF where
    isQuantified' _ = F.Const (Any False)
    freevars' (Var n s) = F.Const [DynamicallySorted s . inject $ Var n s]

instance MaybeQuantified (UniversalF v) where
    isQuantified' _ = F.Const (Any True)
    freevars' (Forall vs a) = F.Const . P.filter (`notElem` map (\v@(IFix (Var _ s)) -> DynamicallySorted s v) vs) . F.getConst $ a

instance MaybeQuantified (ExistentialF v) where
    isQuantified' _ = F.Const (Any True)
    freevars' (Exists vs a) = F.Const . P.filter (`notElem` map (\v@(IFix (Var _ s)) -> DynamicallySorted s v) vs) . F.getConst $ a

instance ( MaybeQuantified f, MaybeQuantified g ) => MaybeQuantified (f :+: g) where
    isQuantified' (InL fa) = isQuantified' fa
    isQuantified' (InR gb) = isQuantified' gb
    freevars' (InL fa) = freevars' fa
    freevars' (InR fb) = freevars' fb

instance {-# OVERLAPPABLE #-} ( IFunctor f, IFoldable f ) => MaybeQuantified f where
    isQuantified' = ifold . imap (isQuantified' . unIFix)
    freevars' = ifold

-- | Test whether an expression contains a quantifier.
isQuantified :: MaybeQuantified f => IFix f s -> Bool
isQuantified = getAny . F.getConst . isQuantified' . unIFix

-- | Tests whether an expression is free of any quantifier.
isQuantifierFree :: MaybeQuantified f => IFix f s -> Bool
isQuantifierFree = P.not . isQuantified

-- | Collects a list of all free variables occurring in an expression.
freevars :: ( IFunctor f, MaybeQuantified f ) => IFix f s -> [DynamicallySorted VarF]
freevars = nub . F.getConst . icata freevars'

-- | A smart constructor for universally quantified formulae
forall :: UniversalF v :<: f => [Var v] -> IFix f 'BooleanSort -> IFix f 'BooleanSort
forall [] f = f
forall vs f = case match f of
    Just (Forall vs' f') -> forall (vs ++ vs') f'
    Nothing -> inject $ Forall vs f

-- | A smart constructor for existentially quantified formulae
exists :: ExistentialF v :<: f => [Var v] -> IFix f 'BooleanSort -> IFix f 'BooleanSort
exists [] f = f
exists vs f = case match f of
    Just (Exists vs' f') -> exists (vs ++ vs') f'
    Nothing -> inject $ Exists vs f

class HasDual f g where
    dual :: f (IFix g) 'BooleanSort -> IFix g 'BooleanSort

instance HasDual NegationF g where
    dual (Not a) = a

instance ( DisjunctionF :<: g, HasDual g g ) => HasDual ConjunctionF g where
    dual (And as) = or (map (dual . unIFix) as)

instance ( ConjunctionF :<: g, HasDual g g ) => HasDual DisjunctionF g where
    dual (Or os) = and (map (dual . unIFix) os)

instance ( ExistentialF v :<: g, HasDual g g ) => HasDual (UniversalF v) g where
    dual (Forall vs a) = exists vs (dual . unIFix $ a)

instance ( UniversalF v :<: g, HasDual g g ) => HasDual (ExistentialF v) g where
    dual (Exists vs a) = forall vs (dual . unIFix $ a)

instance ( HasDual f h, HasDual g h ) => HasDual (f :+: g) h where
    dual (InL fa) = dual fa
    dual (InR gb) = dual gb

instance {-# OVERLAPPABLE #-} ( f :<: g, NegationF :<: g ) => HasDual f g where
    dual = not . inject

class    ( NegationF :<: f, HasDual f f ) => NNF f
instance ( NegationF :<: f, HasDual f f ) => NNF f

-- | Propagates negation toward boolean atoms (across conjunction, disjunction, quantifiers).
nnf :: forall f. NNF f => IFix f 'BooleanSort -> IFix f 'BooleanSort
nnf = nnf' where

    nnf' :: IFix f s -> IFix f s
    nnf' (IFix f) = case index f %~ SBooleanSort of
        Proved Refl -> fromJust $ ( match (IFix f) >>= not' ) <|> Just (IFix (imap nnf' f))
        Disproved _ -> IFix (imap nnf' f)

    not' :: NegationF (IFix f) 'BooleanSort -> Maybe (IFix f 'BooleanSort)
    not' (Not a) = return . dual . unIFix $ a

freename :: forall f (s :: Sort). ( VarF :<: f, IFunctor f, IFoldable f ) => IFix f s -> String
freename a = head $ dropWhile (\s -> any (>= s) ns) pool where
    fs = vars a
    ns = sort $ map (\(DynamicallySorted _ (IFix (Var n _))) -> takeWhile (`elem` ['a'..'z']) n) fs

    pool = [ [x] | x <- ['a'..'z'] ] ++ [ x ++ [y] | x <- pool, y <- ['a'..'z'] ]

type VariableNamePool = Coiter String

rename :: VariableNamePool -> [Var v] -> ([Var v], VariableNamePool)
rename pool = foldl (\(vs, ns) (IFix (Var _ s)) -> let (n', ns') = runCoiter ns in (IFix (Var n' s) : vs, ns')) ([], pool)

freenames :: forall f (s :: Sort). ( VarF :<: f, IFunctor f, IFoldable f ) => IFix f s -> VariableNamePool
freenames a = fmap (\n -> freename a ++ show n) $ unfold (succ . runIdentity) (Identity (0 :: Int))

pushQuantifier' :: ( VarF :<: f, IEq1 f ) => ([Var v] -> IFix f 'BooleanSort -> IFix f 'BooleanSort) -> [Var v] -> IFix f 'BooleanSort -> State (VariableNamePool, IFix f 'BooleanSort -> IFix f 'BooleanSort) (IFix f 'BooleanSort)
pushQuantifier' c vs a = do
    (ns, q) <- get

    let (vs', ns') = rename ns vs
        q'         = c vs' . q
        sub        = mconcat $ zipWith (\(IFix (Var n s)) (IFix (Var n' _)) -> inject (Var n' s) `for` inject (Var n s)) vs vs'

    put (ns', q')

    return $ a `substitute` sub

class MaybeQuantified f => MaybeQuantified' f g where
    pushQuantifier :: f (IFix g) s -> State (VariableNamePool, IFix g 'BooleanSort -> IFix g 'BooleanSort) (IFix g s)

instance ( VarF :<: g, UniversalF v :<: g, IEq1 g ) => MaybeQuantified' (UniversalF v) g where
    pushQuantifier (Forall vs a) = pushQuantifier' forall vs a

instance ( VarF :<: g, ExistentialF v :<: g, IEq1 g ) => MaybeQuantified' (ExistentialF v) g where
    pushQuantifier (Exists vs a) = pushQuantifier' exists vs a

instance ( MaybeQuantified' f h, MaybeQuantified' g h ) => MaybeQuantified' (f :+: g) h where
    pushQuantifier (InL fa) = pushQuantifier fa
    pushQuantifier (InR gb) = pushQuantifier gb

instance {-# OVERLAPPABLE #-} ( f :<: g, IFoldable f ) => MaybeQuantified' f g where
    pushQuantifier = return . inject

class    ( VarF :<: f, NegationF :<: f, IFunctor f, IFoldable f, ITraversable f, HasDual f f, MaybeQuantified' f f ) => Prenex f
instance ( VarF :<: f, NegationF :<: f, IFunctor f, IFoldable f, ITraversable f, HasDual f f, MaybeQuantified' f f ) => Prenex f

-- | Puts an expression into prenex form (quantifier prefix and a quantifier-free formula).
prenex :: forall f. Prenex f => IFix f 'BooleanSort -> IFix f 'BooleanSort
prenex f = let (a, (_, q)) = runState (imapM (pushQuantifier . unIFix) (nnf f)) (freenames f, id) in q a

class Bind f g where
    bind :: Proxy f -> IFix g s -> Maybe (Bool, State (VariableNamePool, [([DynamicallySorted VarF], IFix g 'BooleanSort -> IFix g 'BooleanSort)]) (IFix g s))

instance forall g v. ( VarF :<: g, EqualityF :<: g, NegationF :<: g, DisjunctionF :<: g, UniversalF v :<: g, MaybeQuantified g, SingI v ) => Bind (UniversalF v) g where
    bind _ a = case index (unIFix a) %~ (sing :: Sing v) of
        Proved Refl -> Just . (\s -> (False, s)) $ do
            (ns, q) <- get

            let x :: forall f. VarF :<: f => IFix f v
                x = var n

                (n, ns') = runCoiter ns

            put (ns', (freevars a, forall [x] . (x .=. a .->.)) : q)
            return x
        Disproved _ -> Nothing

instance forall g v. ( VarF :<: g, EqualityF :<: g, ConjunctionF :<: g, ExistentialF v :<: g, MaybeQuantified g, SingI v ) => Bind (ExistentialF v) g where
    bind _ a = case index (unIFix a) %~ (sing :: Sing v) of
        Proved Refl -> Just . (\s -> (True, s)) $ do
            (ns, q) <- get

            let x :: forall f. VarF :<: f => IFix f v
                x = var n

                (n, ns') = runCoiter ns

            put (ns', (freevars a, exists [x] . (x .=. a .&.)) : q)
            return x
        Disproved _ -> Nothing

instance ( Bind f h, Bind g h ) => Bind (f :+: g) h where
    bind _ a = let ls = bind (Proxy :: Proxy f) a
                   rs = bind (Proxy :: Proxy g) a in merge ls rs where

        merge Nothing m = m
        merge m Nothing = m

        merge m@(Just (True, _)) _ = m
        merge _ m@(Just (True, _)) = m

        merge m _ = m

instance {-# OVERLAPPABLE #-} Bind f g where
    bind _ _ = Nothing

class Bind' f g where
    bind' :: Bind g g => f (IFix g) s -> Maybe (Bool, State (VariableNamePool, [([DynamicallySorted VarF], IFix g 'BooleanSort -> IFix g 'BooleanSort)]) (IFix g s))

instance VarF :<: g => Bind' VarF g where
    bind' v = Just (True, return . inject $ v)

instance ArithmeticF :<: g => Bind' ArithmeticF g where
    bind' c@Const {} = Just (True, return . inject $ c)
    bind' a = bind (Proxy :: Proxy g) (inject a)

instance ConjunctionF :<: g => Bind' ConjunctionF g where
    bind' a@(And []) = Just (True, return . inject $ a)
    bind' a = bind (Proxy :: Proxy g) (inject a)

instance DisjunctionF :<: g => Bind' DisjunctionF g where
    bind' a@(Or []) = Just (True, return . inject $ a)
    bind' a = bind (Proxy :: Proxy g) (inject a)

instance ( Bind' f h, Bind' g h ) => Bind' (f :+: g) h where
    bind' (InL fa) = bind' fa
    bind' (InR gb) = bind' gb

instance {-# OVERLAPPABLE #-} f :<: g => Bind' f g where
    bind' a = bind (Proxy :: Proxy g) (inject a)

bind'' :: forall f (s :: Sort). ( Bind f f, Bind' f f ) => IFix f s -> State (VariableNamePool, [([DynamicallySorted VarF], IFix f 'BooleanSort -> IFix f 'BooleanSort)]) (IFix f s)
bind'' a = fromMaybe (return a) . fmap snd . bind' . unIFix $ a

class MaybeQuantified'' f g where
    flatten' :: ( Bind g g, Bind' g g ) => f (IFix g) s -> State (VariableNamePool, [([DynamicallySorted VarF], IFix g 'BooleanSort -> IFix g 'BooleanSort)]) (IFix g s)

instance ArrayF :<: g => MaybeQuantified'' ArrayF g where
    flatten' (Select is es a i) = do
        a' <- bind'' a
        i' <- bind'' i
        return . inject $ Select is es a' i'
    flatten' (Store is es a i e) = do
        a' <- bind'' a
        i' <- bind'' i
        e' <- bind'' e
        return . inject $ Store is es a' i' e'

instance ( UniversalF v :<: g, SingI v ) => MaybeQuantified'' (UniversalF v) g where
    flatten' (Forall vs a) = do
        (ns, qs) <- get

        let (d, i) = partition (\(vs', _) -> any (`elem` mapMaybe toStaticallySorted vs') vs) qs

        put (ns, i)

        return $ forall vs (foldr snd a d)

instance ( ExistentialF v :<: g, SingI v ) => MaybeQuantified'' (ExistentialF v) g where
    flatten' (Exists vs a) = do
        (ns, qs) <- get

        let (d, i) = partition (\(vs', _) -> any (`elem` mapMaybe toStaticallySorted vs') vs) qs

        put (ns, i)

        return $ exists vs (foldr snd a d)

instance ( MaybeQuantified'' f h, MaybeQuantified'' g h ) => MaybeQuantified'' (f :+: g) h where
    flatten' (InL fa) = flatten' fa
    flatten' (InR gb) = flatten' gb

instance {-# OVERLAPPABLE #-} f :<: g => MaybeQuantified'' f g where
    flatten' = return . inject

class    ( VarF :<: f, Bind f f, Bind' f f, MaybeQuantified'' f f, IFoldable f, ITraversable f ) => Flatten f
instance ( VarF :<: f, Bind f f, Bind' f f, MaybeQuantified'' f f, IFoldable f, ITraversable f ) => Flatten f

-- | Replaces non-variable and non-constant arguments to uninterpreted functions (such as `select` and `store`) with a fresh bound (universally or existentially) variable that is bound to the original term.
flatten :: forall f. Flatten f => IFix f 'BooleanSort -> IFix f 'BooleanSort
flatten f = let (a, (_, qs)) = runState (imapM flatten'' f) (freenames f, []) in foldr snd a qs where
    flatten'' f' = do
        (ns, q) <- get
        put (ns, [])
        r <- flatten' (unIFix f')
        (ns', q') <- get
        put (ns', q ++ q')
        return r

class Forall f g where
    quantify :: Proxy f -> Sing s -> Maybe ([Var s] -> IFix g 'BooleanSort -> IFix g 'BooleanSort)

instance ( UniversalF v :<: g, SingI v ) => Forall (UniversalF v) g where
    quantify _ s = case s %~ (sing :: Sing v) of
        Proved Refl -> Just forall
        Disproved _ -> Nothing

instance ( Forall f h, Forall g h ) => Forall (f :+: g) h where
    quantify _ s = quantify (Proxy :: Proxy f) s <|> quantify (Proxy :: Proxy g) s

instance {-# OVERLAPPABLE #-} Forall f g where
    quantify _ _ = Nothing

class Axiomatized f g where
    instantiate :: Forall g g => IFix g s -> f (IFix g) s -> Maybe (State VariableNamePool (IFix g 'BooleanSort))

instance ( VarF :<: g, ConjunctionF :<: g, DisjunctionF :<: g, NegationF :<: g, EqualityF :<: g, ArrayF :<: g ) => Axiomatized ArrayF g where
    instantiate a' (Store (is :: Sing is) es a i e) = case quantify (Proxy :: Proxy g) is of
        Just q -> Just $ do
            ns <- get

            let j :: forall f. VarF :<: f => IFix f is
                j = inject $ Var n is

                (n, ns') = runCoiter ns

            put ns'

            return $ inject (Equals es (inject (Select is es a' i)) e) .&. q [j] (not (inject (Equals is i j)) .->. inject (Equals es (inject (Select is es a' j)) (inject (Select is es a j))))
        Nothing -> Nothing
    instantiate _ _ = Nothing

instance ( Axiomatized f h, Axiomatized g h ) => Axiomatized (f :+: g) h where
    instantiate v (InL fa) = instantiate v fa
    instantiate v (InR gb) = instantiate v gb

instance {-# OVERLAPPABLE #-} Axiomatized f g where
    instantiate _ _ = Nothing

class    ( VarF :<: f, EqualityF :<: f, Bind f f, Bind' f f, MaybeQuantified'' f f, Forall f f, Axiomatized f f, IFoldable f, ITraversable f ) => Unstore f
instance ( VarF :<: f, EqualityF :<: f, Bind f f, Bind' f f, MaybeQuantified'' f f, Forall f f, Axiomatized f f, IFoldable f, ITraversable f ) => Unstore f

-- | Replaces `store` with an instance of its axiomatization.
unstore :: forall f. Unstore f => IFix f 'BooleanSort -> IFix f 'BooleanSort
unstore a = let a' = flatten a in evalState (imapM unstore' a') (freenames a') where
    unstore' :: IFix f s -> State VariableNamePool (IFix f s)
    unstore' a' = fromMaybe (return a') (match a' >>= \(Equals _ l r) -> instantiate l (unIFix r) <|> instantiate r (unIFix l))
