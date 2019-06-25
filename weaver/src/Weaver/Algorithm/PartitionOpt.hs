{-# LANGUAGE
    BlockArguments,
    FlexibleContexts,
    MonoLocalBinds,
    ScopedTypeVariables,
    TupleSections,
    UnicodeSyntax,
    ViewPatterns
  #-}

module Weaver.Algorithm.PartitionOpt where

import           Data.Automata.DFA (DFA, Edge (..), approximate, difference, find)
import           Data.Automata.NFA (toDFA)
import           Data.Automata.Graph (foldCut, optimize)
import           Data.Finite.Container (Container, Index)
import qualified Data.Finite.Set as Set
import           Data.Finite.Set.Antichain (Antichain)
import qualified Data.Finite.Set.Antichain as AC
import           Data.Finite.Small.Map (Map)
import           Data.List (foldl', subsequences)
import           Data.Key (index, toKeyedList)
import           Weaver.Algorithm (Algorithm (..), Interface (..))
import           Weaver.Algorithm.PartitionProgress (Proof, initialize, size, generalize)
import           Weaver.Counterexample (Counterexample (..), singleton)

algorithm ∷ Algorithm
algorithm = Algorithm \solver program → Interface
  (initialize solver)
  size
  (check program)
  (generalize solver)

check ∷ ∀c a. Container c a ⇒ DFA (Map (Index c)) → Proof c -> Counterexample c
check programDFA (deps, _, πNFA)
  | AC.isEmpty (foldCut go AC.empty (not . AC.isEmpty) diff) = mempty
  | otherwise = maybe mempty singleton (find diff)
  where go ∷ (r → Antichain (Index c)) → Edge (Map (Index c)) r → Antichain (Index c)
        go _ (Edge _ True)  = AC.universe
        go k (Edge δ False) = foldl'
          (\old xs →
            let set = Set.complement (Set.fromList (map fst xs)) in
            case AC.tryInsert set old of
              Just new | all (\(a, v) → any (\s → Set.isSubsetOf set (Set.union s (index deps a))) (AC.toList (k v))) xs → new
              _ → old)
          AC.empty
          (tail (subsequences (toKeyedList δ)))

        diff = approximate (optimize (difference programDFA (toDFA πNFA)))
