{-# LANGUAGE
    BlockArguments,
    DeriveTraversable,
    FlexibleContexts,
    MonoLocalBinds,
    PatternSynonyms,
    ScopedTypeVariables,
    UnicodeSyntax
  #-}

module Weaver.Algorithm.PartitionSets (algorithm, check) where

import           Control.Monad (guard)
import           Data.Automata.DFA (DFA, Edge (..), approximate, difference, find)
import qualified Data.Automata.NFA as NFA
import           Data.Automata.Graph (pattern Unfold, foldCut, optimize, unfold)
import qualified Data.Automata.Regex as Regex
import           Data.Finite.Container (Container, Index)
import           Data.Finite.Set (Set)
import qualified Data.Finite.Set as Set
import           Data.Finite.Small.Map (Map, keys)
import           Data.List (subsequences)
import           Data.Key (index, toKeyedList)
import           Weaver.Algorithm (Algorithm (..), Interface (..))
import           Weaver.Algorithm.PartitionProgress (Proof, initialize, size, generalize, shrink)
import           Weaver.Algorithm.Normal (display)
import           Weaver.Counterexample (Counterexample (..), singleton)

algorithm ∷ Algorithm
algorithm = Algorithm \solver program → Interface
  (initialize solver)
  size
  (check (Regex.toDFA program))
  (generalize solver)
  (\(_, φs, _) → display φs)
  (shrink solver)

check ∷ ∀c a. Container c a ⇒ DFA (Map (Index c)) → Proof c -> Counterexample c
check programDFA (deps, _, πNFA)
  | check' deps diff = mempty
  | otherwise = maybe mempty singleton (find diff)
  where diff = approximate (optimize (difference programDFA (NFA.toDFA πNFA)))

newtype Lists a = Lists [[a]]
  deriving (Foldable, Functor, Traversable)

check' ∷ ∀c a. Container c a ⇒ Map (Index c) (Set (Index c)) → DFA (Map (Index c)) → Bool
check' deps (Unfold next (root ∷ q)) =
    not (foldCut go₁ False id (unfold go₂ (root, Set.empty))) where
  go₁ ∷ (r → Bool) → Lists r → Bool
  go₁ k (Lists xs) = all (any k) xs

  go₂ ∷ (q, Set (Index c)) → Lists (q, Set (Index c))
  go₂ (q, s) =
    case next q of
      Edge _ True  → Lists []
      Edge δ False → Lists do
        part ← map Set.fromList (subsequences (keys δ))
        return do
          (a, q') ← toKeyedList δ
          guard (not (Set.member a s))
          let orderₐ = if Set.member a part then Set.empty else part
              depsₐ = index deps a
          return (q', Set.difference (Set.union s orderₐ) depsₐ)
