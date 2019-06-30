{-# LANGUAGE
    BlockArguments,
    FlexibleContexts,
    MonoLocalBinds,
    ScopedTypeVariables,
    TupleSections,
    UnicodeSyntax,
    ViewPatterns
  #-}

module Weaver.Algorithm.PartitionProgressTrace where

import           Prelude hiding (lookup)
import           Control.Monad (filterM)
import           Data.Automata.DFA (DFA, Edge (..))
import           Data.Automata.Graph (foldCut)
import           Data.Finite.Container (Container, Index, lookup)
import           Data.Finite.Class (universe)
import           Data.Finite.Set (Set)
import qualified Data.Finite.Set as Set
import           Data.Finite.Set.AntiMap (AntiMap)
import qualified Data.Finite.Set.AntiMap as AM
import           Data.Finite.Small.Map (Map, keys)
import qualified Data.Finite.Small.Map as Map
import           Data.List (subsequences)
import           Data.Key (index, toKeyedList)
import           Data.Maybe (fromMaybe)
import           Language.SMT.Expr (true)
import           Weaver.Algorithm (Algorithm (..), Assertions, Solver' (..), Interface (..))
import qualified Weaver.Algorithm.NormalTrace as NormalTrace
import           Weaver.Counterexample (Counterexample (..), extend)
import           Weaver.Program (Tag, conflicts)
import           Weaver.Stmt (Stmt)

algorithm ∷ Algorithm
algorithm = Algorithm \solver program → Interface
  (initialize solver program)
  size
  check
  (generalize solver)
  (const (return ()))

type Proof c = (Map (Index c) (Set (Index c)), NormalTrace.Proof c)

initialize ∷ ∀c. Container c ([Tag], Stmt) ⇒ Solver' → DFA (Map (Index c)) → Assertions → IO (Proof c)
initialize solver program φs = do
  let stmts = universe

      isDependent (lookup → (tag₁, stmt₁)) (lookup → (tag₂, stmt₂))
        | conflicts tag₁ tag₂ = return True
        | otherwise = not <$> isIndep' solver true stmt₁ stmt₂

  deps ← mapM (\stmt → (stmt,) <$> filterM (isDependent stmt) stmts) stmts
  (fmap Set.fromList (Map.fromList deps),) <$> NormalTrace.initialize solver program φs

size ∷ Proof c → Int
size (_, π) = NormalTrace.size π

check ∷ ∀c a. Container c a ⇒ Proof c -> Counterexample c
check (deps, π) =
    fromMaybe mempty
    . AM.lookup Set.empty
    $ foldCut go AM.empty (not . AM.isEmpty) π
  where go ∷ (r → AntiMap (Index c) (Counterexample c)) → Edge (Map (Index c)) r → AntiMap (Index c) (Counterexample c)
        go _ (Edge _ True)  = AM.universe Nil
        go k (Edge δ False) = AM.intersectionsWith (<>) mempty do
          part ← map Set.fromList (subsequences (keys δ))
          return . AM.unions $ do
            (a, q) ← toKeyedList δ
            (pₘₐₓ, xss) ← AM.toList (k q)
            let orderₐ = if Set.member a part then Set.empty else part
                depsₐ = index deps a
            return $
              if Set.isSubsetOf (Set.difference orderₐ depsₐ) pₘₐₓ
              then AM.singleton (Set.delete a (Set.unions [pₘₐₓ, orderₐ, depsₐ])) (extend a xss)
              else AM.empty

generalize ∷ Container c ([Tag], Stmt) ⇒ Solver' → [Assertions] → Proof c → IO (Proof c)
generalize solver φs (deps, π) = (deps,) <$> NormalTrace.generalize solver φs π
