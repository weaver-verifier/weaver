{-# LANGUAGE
    BlockArguments,
    FlexibleContexts,
    MonoLocalBinds,
    ScopedTypeVariables,
    TupleSections,
    UnicodeSyntax,
    ViewPatterns
  #-}

module Weaver.Algorithm.Partition where

import           Data.Automata.DFA (DFA, Edge (..), approximate, difference, find)
import qualified Data.Automata.NFA as NFA
import           Data.Automata.Graph (foldCut, optimize)
import qualified Data.Automata.Regex as Regex
import           Data.Finite.Container (Container, Index)
import qualified Data.Finite.Set as Set
import           Data.Finite.Set.Antichain (Antichain)
import qualified Data.Finite.Set.Antichain as AC
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
  | AC.isEmpty (foldCut go AC.empty (not . AC.isEmpty) diff) = mempty
  | otherwise = maybe mempty singleton (find diff)
  where go ∷ (r → Antichain (Index c)) → Edge (Map (Index c)) r → Antichain (Index c)
        go _ (Edge _ True)  = AC.universe
        go k (Edge δ False) = AC.intersections do
          part ← map Set.fromList (subsequences (keys δ))
          return . AC.unions $ do
            (a, q) ← toKeyedList δ
            pₘₐₓ ← AC.toList (k q)
            let orderₐ = if Set.member a part then Set.empty else part
                depsₐ = index deps a
            return $
              if Set.isSubsetOf (Set.difference orderₐ depsₐ) pₘₐₓ
              then AC.singleton (Set.delete a (Set.unions [pₘₐₓ, orderₐ, depsₐ]))
              else AC.empty

        diff = approximate (optimize (difference programDFA (NFA.toDFA πNFA)))
