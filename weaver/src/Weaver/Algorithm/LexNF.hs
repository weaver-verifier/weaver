{-# LANGUAGE
    BlockArguments,
    FlexibleContexts,
    ImplicitParams,
    MonoLocalBinds,
    ScopedTypeVariables,
    TupleSections,
    UnicodeSyntax,
    ViewPatterns
  #-}

module Weaver.Algorithm.LexNF where

import           Prelude hiding (lookup)
import           Data.Automata.DFA (DFA, Edge (..), approximate, difference)
import           Data.Automata.NFA (toDFA)
import           Data.Automata.Graph (foldCut, optimize)
import           Data.Finite.Container (Container, Index)
import qualified Data.Finite.Set as Set
import           Data.Finite.Set.AntiMap (AntiMap)
import qualified Data.Finite.Set.AntiMap as AM
import           Data.Finite.Small.Map (Map, keys)
import           Data.Key (index, toKeyedList)
import           Data.Maybe (fromMaybe)
import           Weaver.Algorithm (Algorithm (..), Interface (..))
import qualified Weaver.Algorithm.Normal as Normal
import           Weaver.Algorithm.PartitionProgress (Proof, initialize, size, generalize, shrink)
import           Weaver.Counterexample (Counterexample (..), extend)

algorithm ∷ Algorithm
algorithm = Algorithm \solver program → Interface
  (initialize solver)
  size
  (check program)
  (generalize solver)
  (\(_, φs, _) → Normal.display φs)
  (shrink solver)

check ∷ ∀c a. Container c a ⇒ DFA (Map (Index c)) → Proof c -> Counterexample c
check programDFA (deps, _, πNFA) =
    fromMaybe mempty
    . AM.lookup Set.empty
    . foldCut go AM.empty (not . AM.isEmpty)
    . approximate . optimize . difference programDFA
    $ toDFA πNFA
  where go ∷ (r → AntiMap (Index c) (Counterexample c)) → Edge (Map (Index c)) r → AntiMap (Index c) (Counterexample c)
        go _ (Edge _ True)  = AM.universe Nil
        go k (Edge δ False) = AM.unions do
            (a, q) ← toKeyedList δ
            (pₘₐₓ, xss) ← AM.toList (k q)
            let orderₐ = Set.fromList (dropWhile (/= a) order)
                depsₐ = index deps a
            return $
              if Set.isSubsetOf (Set.difference orderₐ depsₐ) pₘₐₓ
              then AM.singleton (Set.delete a (Set.unions [pₘₐₓ, orderₐ, depsₐ])) (extend a xss)
              else AM.empty
          where order = keys δ
