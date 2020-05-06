{-# LANGUAGE
    BlockArguments,
    FlexibleContexts,
    MonoLocalBinds,
    ScopedTypeVariables,
    TupleSections,
    UnicodeSyntax,
    ViewPatterns
  #-}

module Weaver.Algorithm.TotalProgressContextOpt where

import           Prelude hiding (lookup)
import           Control.Monad (guard)
import           Data.Automata.DFA (Edge (..), approximate, difference)
import           Data.Automata.NFA (toDFA)
import           Data.Automata.Graph (foldCut, optimize)
import           Data.Finite.Container (Container, Index, lookup)
import qualified Data.Finite.Set as Set
import           Data.Finite.Set.AntiMap (AntiMap)
import qualified Data.Finite.Set.AntiMap as AM
import           Data.Foldable (asum)
import           Data.List (foldl', subsequences)
import           Data.Key (index, toKeyedList)
import           Data.Maybe (fromMaybe)
import           Weaver.Algorithm (Algorithm (..), Interface (..))
import           Weaver.Algorithm.PartitionProgressContext (Proof, IMap (..), initialize, size, generalize, shrink)
import           Weaver.Algorithm.Normal (display)
import           Weaver.Counterexample (Counterexample (..), extend')
import           Weaver.Program (Tag, conflicts)
import           Weaver.Stmt (Stmt)

algorithm ∷ Algorithm
algorithm = Algorithm \solver program → Interface
  (initialize solver program)
  size
  check
  (generalize solver)
  (\(_, φs, _) → display φs)
  (shrink solver)

check ∷ ∀c. Container c ([Tag], Stmt) ⇒ Proof c -> Counterexample c
check (programDFA, _, πNFA) =
    fromMaybe mempty
    . AM.lookup Set.empty
    . foldCut go AM.empty (not . AM.isEmpty)
    . approximate . optimize . difference programDFA
    $ toDFA πNFA
  where go ∷ (r → AntiMap (Index c) (Counterexample c)) → Edge (IMap c) r → AntiMap (Index c) (Counterexample c)
        go _ (Edge _ True)  = AM.universe Nil
        go k (Edge (IMap indeps δ) False) = foldl'
          (\old xs →
            let set = Set.complement (Set.fromList (map fst xs)) in
            if AM.member set old
            then old
            else case mapM (\(a, v) → asum (map (\(s, c) → extend' (Set.mapStrongFst a (Set.filter (not . conflicts (fst (lookup a)) . fst . lookup) s)) a c <$ guard (Set.isSubsetOf set (Set.union s (Set.complement (index indeps a))))) (AM.toList (k v)))) xs of
                   Nothing → old
                   Just cs → AM.insert set (mconcat cs) old)
          AM.empty
          (tail (subsequences (toKeyedList δ)))
