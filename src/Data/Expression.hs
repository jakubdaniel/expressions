{-# LANGUAGE DataKinds
           , FlexibleContexts
           , FlexibleInstances
           , GADTs
           , MultiParamTypeClasses
           , OverloadedStrings
           , RankNTypes
           , ScopedTypeVariables
           , TypeInType
           , TypeOperators #-}

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
                       , disjuncts ) where

import Algebra.Lattice
import Control.Applicative
import Control.Monad.Trans.Class
import Control.Monad.Trans.Reader
import Data.List hiding (and, or, union)
import Data.Map hiding (map, foldr)
import Data.Maybe
import Data.Monoid
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

instance ComplementedLattice (QFLogic 'BooleanSort) where complement = not
instance ComplementedLattice (QFLia   'BooleanSort) where complement = not
instance ComplementedLattice (  Lia   'BooleanSort) where complement = not
instance ComplementedLattice (QFALia  'BooleanSort) where complement = not
instance ComplementedLattice (  ALia  'BooleanSort) where complement = not

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

instance Monoid (Substitution f) where
    mempty  = Substitution (const Nothing)
    (Substitution f) `mappend` (Substitution g) = Substitution $ \a -> getFirst (mconcat ([First . f, First . g] <*> [a]))

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
        true'  = string "true"  *> pure (DynamicallySorted SBooleanSort $ true)

        and' = do
            _  <- char '(' *> string "and" *> space
            as <- r `sepBy1` space
            _  <- char ')'
            and'' as

        and'' as = case mapM toStaticallySorted as of
            Just as' -> return . DynamicallySorted SBooleanSort $ and as'
            Nothing  -> fail "and of non-boolean arguments"

instance DisjunctionF :<: f => Parseable DisjunctionF f where
    parser _ r = choice [ false', or' ] <?> "Disjunction" where
        false' = string "false" *> pure (DynamicallySorted SBooleanSort $ false)

        or' = do
            _  <- char '(' *> string "or" *> space
            os <- r `sepBy1` space
            _  <- char ')'
            or'' os

        or'' os = case mapM toStaticallySorted os of
            Just os' -> return . DynamicallySorted SBooleanSort $ or os'
            Nothing  -> fail "or of non-boolean arguments"

instance NegationF :<: f => Parseable NegationF f where
    parser _ r = not' <?> "Negation" where
        not' = do
            _ <- char '(' *> string "not" *> space
            n <- r
            _ <- char ')'
            not'' n

        not'' n = case toStaticallySorted n of
            Just n' -> return . DynamicallySorted SBooleanSort $ not n'
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
a .&. b = merge (flatten a ++ flatten b) where
    merge []  = true
    merge [f] = f
    merge as  = inject $ And as

    flatten e = case match e of
        Just (And as) -> as
        _ -> [e]

-- | A smart constructor for binary disjunction
(.|.) :: DisjunctionF :<: f => IFix f 'BooleanSort -> IFix f 'BooleanSort -> IFix f 'BooleanSort
a .|. b = merge (flatten a ++ flatten b) where
    merge []  = false
    merge [f] = f
    merge os  = inject $ Or os

    flatten e = case match e of
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
                Just phi' -> return . DynamicallySorted SBooleanSort $ forall vs' phi'
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
                Just phi' -> return . DynamicallySorted SBooleanSort $ exists vs' phi'
                Nothing   -> fail "quantifying non-boolean expression"
            Nothing  -> fail "ill-sorted quantifier"

        context (DynamicallySorted s v) = case match v of
            Just (Var n _) -> (n, DynamicSort s)
            _              -> error "impossible error"

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
