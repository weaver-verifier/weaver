{-# LANGUAGE
    BlockArguments,
    DeriveTraversable,
    FlexibleContexts,
    MonoLocalBinds,
    PatternSynonyms,
    ScopedTypeVariables,
    UnicodeSyntax
  #-}

module Weaver.Algorithm.PartitionProgressSets (algorithm, check) where

import           Control.Monad (guard)
import           Data.Automata.DFA (DFA, Edge (..), approximate, difference)
import qualified Data.Automata.NFA as NFA
import           Data.Automata.Graph (pattern Unfold, foldCut, optimize, unfold)
import qualified Data.Automata.Regex as Regex
import           Data.Finite.Container (Container, Index)
import           Data.Finite.Set (Set)
import qualified Data.Finite.Set as Set
import           Data.Finite.Small.Map (Map, keys, fromListWith)
import           Data.Foldable (asum)
import           Data.List (subsequences)
import           Data.Maybe (fromMaybe, isJust)
import           Data.Key (index, toKeyedList)
import           Weaver.Algorithm (Algorithm (..), Interface (..))
import           Weaver.Algorithm.PartitionProgress (Proof, initialize, size, generalize, shrink)
import           Weaver.Algorithm.Normal (display)
import           Weaver.Counterexample (Counterexample (..))

algorithm ∷ Algorithm
algorithm = Algorithm \solver program → Interface
  (initialize solver)
  size
  (check (Regex.toDFA program))
  (generalize solver)
  (\(_, φs, _) → display φs)
  (shrink solver)

check ∷ ∀c a. Container c a ⇒ DFA (Map (Index c)) → Proof c -> Counterexample c
check programDFA (deps, _, πNFA) = check' deps diff
  where diff = approximate (optimize (difference programDFA (NFA.toDFA πNFA)))

data Lists' k v = Lists' [[(k, v)]]
  deriving (Foldable, Functor, Traversable)

check' ∷ ∀c a. Container c a ⇒ Map (Index c) (Set (Index c)) → DFA (Map (Index c)) → Counterexample c
check' deps (Unfold next (root ∷ q)) =
  fromMaybe mempty (foldCut go₁ Nothing isJust (unfold go₂ (root, Set.empty))) where
    go₁ ∷ (r → Maybe (Counterexample c)) → Lists' (Index c) r → Maybe (Counterexample c)
    go₁ k (Lists' xs) = do
      ys ← traverse (asum . map (traverse k)) xs
      case ys of
        [] → return Nil
        _  → return (Cons mempty (fromListWith (<>) ys))

    go₂ ∷ (q, Set (Index c)) → Lists' (Index c) (q, Set (Index c))
    go₂ (q, s) =
      case next q of
        Edge _ True  → Lists' []
        Edge δ False → Lists' do
          part ← map Set.fromList (subsequences (keys δ))
          return do
            (a, q') ← toKeyedList δ
            guard (not (Set.member a s))
            let orderₐ = if Set.member a part then Set.empty else part
                depsₐ = index deps a
            return (a, (q', Set.difference (Set.union s orderₐ) depsₐ))
