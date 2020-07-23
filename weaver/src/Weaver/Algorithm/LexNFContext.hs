{-# LANGUAGE
    BlockArguments,
    DeriveTraversable,
    FlexibleContexts,
    ImplicitParams,
    MonoLocalBinds,
    PatternSynonyms,
    RecordWildCards,
    ScopedTypeVariables,
    TupleSections,
    UnicodeSyntax,
    ViewPatterns
  #-}

module Weaver.Algorithm.LexNFContext where

import           Data.Automata.DFA (Edge (..), approximate, difference)
import           Data.Automata.NFA (toDFA)
import           Data.Automata.Graph (foldCut, optimize)
import qualified Data.Automata.Regex as Regex
import           Data.Finite.Container (Container, Index)
import qualified Data.Finite.Set as Set
import           Data.Finite.Set.AntiMap (AntiMap)
import qualified Data.Finite.Set.AntiMap as AM
import           Data.Finite.Small.Map (keys)
import           Data.Key (index, toKeyedList)
import           Data.Maybe (fromMaybe)
import           Weaver.Algorithm (Algorithm (..), Interface (..))
import qualified Weaver.Algorithm.Normal as Normal
import           Weaver.Algorithm.PartitionProgressContext (Proof, IMap (..), initialize, size, generalize, shrink)
import           Weaver.Counterexample (Counterexample (..), extend)
import           Weaver.Program (Tag)
import           Weaver.Stmt (Stmt)

algorithm ∷ Algorithm
algorithm = Algorithm \solver program → Interface
  (initialize solver (Regex.toDFA program))
  size
  check
  (generalize solver)
  (\(_, φs, _) → Normal.display φs)
  (shrink solver)

check ∷ ∀c. Container c ([Tag], Stmt) ⇒ Proof c -> Counterexample c
check (programDFA, _, πNFA) =
    fromMaybe mempty
    . AM.lookup Set.empty
    . foldCut go AM.empty (not . AM.isEmpty)
    . approximate . optimize . difference programDFA
    $ toDFA πNFA
  where go ∷ (r → AntiMap (Index c) (Counterexample c)) → Edge (IMap c) r → AntiMap (Index c) (Counterexample c)
        go _ (Edge _               True)  = AM.universe Nil
        go k (Edge (IMap indeps δ) False) = AM.unions do
            (a, q) ← toKeyedList δ
            (pₘₐₓ, xss) ← AM.toList (k q)
            let orderₐ = Set.fromList (dropWhile (/= a) order)
                depsₐ = Set.complement (index indeps a)
            return $
              if Set.isSubsetOf (Set.difference orderₐ depsₐ) pₘₐₓ
              then AM.singleton (Set.delete a (Set.unions [pₘₐₓ, orderₐ, depsₐ])) (extend a xss)
              else AM.empty
          where order = keys δ
