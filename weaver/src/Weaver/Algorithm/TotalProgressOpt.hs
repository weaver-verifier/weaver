{-# LANGUAGE
    BlockArguments,
    FlexibleContexts,
    MonoLocalBinds,
    ScopedTypeVariables,
    TupleSections,
    UnicodeSyntax,
    ViewPatterns
  #-}

module Weaver.Algorithm.TotalProgressOpt where

import           Control.Monad (guard)
import           Data.Automata.DFA (DFA, Edge (..), approximate, difference)
import           Data.Automata.NFA (toDFA)
import           Data.Automata.Graph (foldCut, optimize)
import           Data.Finite.Container (Container, Index)
import qualified Data.Finite.Set as Set
import           Data.Finite.Set.AntiMap (AntiMap)
import qualified Data.Finite.Set.AntiMap as AM
import           Data.Finite.Small.Map (Map)
import           Data.Foldable (asum)
import           Data.List (foldl', subsequences)
import           Data.Maybe (fromMaybe)
import           Data.Key (index, toKeyedList)
import           Weaver.Algorithm (Algorithm (..), Interface (..))
import           Weaver.Algorithm.PartitionProgress (Proof, initialize, size, generalize)
import           Weaver.Algorithm.Normal (display)
import           Weaver.Counterexample (Counterexample (..), extend)

algorithm ∷ Algorithm
algorithm = Algorithm \solver program → Interface
  (initialize solver)
  size
  (check program)
  (generalize solver)
  (\(_, φs, _) → display φs)

check ∷ ∀c a. Container c a ⇒ DFA (Map (Index c)) → Proof c -> Counterexample c
check programDFA (deps, _, πNFA) =
    fromMaybe mempty
    . AM.lookup Set.empty
    . foldCut go AM.empty (not . AM.isEmpty)
    . approximate . optimize . difference programDFA
    $ toDFA πNFA
  where go ∷ (r → AntiMap (Index c) (Counterexample c)) → Edge (Map (Index c)) r → AntiMap (Index c) (Counterexample c)
        go _ (Edge _ True)  = AM.universe Nil
        go k (Edge δ False) = foldl'
          (\old xs →
            let set = Set.complement (Set.fromList (map fst xs)) in
            if AM.member set old
            then old
            else case mapM (\(a, v) → extend a <$> asum (map (\(s, c) → guard (Set.isSubsetOf set (Set.union s (index deps a))) >> return c) (AM.toList (k v)))) xs of
                   Nothing → old
                   Just cs → AM.insert set (mconcat cs) old)
          AM.empty
          (tail (subsequences (toKeyedList δ)))
