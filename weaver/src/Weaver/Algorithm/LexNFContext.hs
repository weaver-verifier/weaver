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

import           Prelude hiding (lookup)
import           Control.Monad (filterM, when)
import           Data.Align (Align (..))
import           Data.Automata.DFA (DFA, Edge (..), approximate, difference)
import           Data.Automata.Classes (Absorb (..))
import           Data.Automata.NFA (NFA, NFAM, toDFA)
import qualified Data.Automata.NFA as NFA
import           Data.Automata.Graph (pattern Unfold, GraphM (..), foldCut, lower, optimize)
import           Data.Finite.Container (Container, Index, lookup, reify)
import           Data.Finite.Class (universe)
import           Data.Finite.Set (Set)
import qualified Data.Finite.Set as Set
import           Data.Finite.Set.AntiMap (AntiMap)
import qualified Data.Finite.Set.AntiMap as AM
import           Data.Finite.Small.Map (Map, keys)
import qualified Data.Finite.Small.Map as Map
import           Data.Foldable (for_, foldl')
import           Data.Key (index, toKeyedList)
import           Data.Maybe (fromMaybe)
import qualified Data.Set as OrdSet
import           Language.SMT.Expr (true, false)
import           Language.SMT.SExpr (SExpressible (..), pretty, prettyPrint)
import           Text.Printf (printf)
import           Weaver.Algorithm (Algorithm (..), Assertions, Solver' (..), Interface (..))
import           Weaver.Config
import           Weaver.Counterexample (Counterexample (..), extend)
import           Weaver.Program (Tag, conflicts)
import           Weaver.Stmt (Stmt)

algorithm ∷ Algorithm
algorithm = Algorithm \solver program → Interface
  (initialize solver program)
  size
  check
  (generalize solver)

data IMap c q = IMap (Map (Index c) (Set (Index c))) (Map (Index c) q)
  deriving (Foldable, Functor)

instance Absorb (IMap c) where
  absorbWith f (IMap a x) (IMap b y) = IMap
    (Map.unionWith Set.union a b)
    (absorbWith f x y)

instance Align (IMap c) where
  nil = IMap nil nil
  alignWith f (IMap a x) (IMap b y) = IMap
    (Map.unionWith Set.union a b)
    (alignWith f x y)

type Proof c = (DFA (IMap c), Assertions, NFA (IMap c))

initialize ∷ ∀c. (Container c ([Tag], Stmt), ?config ∷ Config) ⇒ Solver' → DFA (Map (Index c)) → Assertions → IO (Proof c)
initialize solver (Unfold next root) φs =
    (program', φs,) <$> lower (proofToNFA solver φs)
  where program' = Unfold next' root
        next' (next → Edge δ q) = Edge (IMap Map.empty δ) q

size ∷ Proof c → Int
size (_, φs, _) = length φs

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

generalize ∷ (Container c ([Tag], Stmt), ?config ∷ Config) ⇒ Solver' → [Assertions] → Proof c → IO (Proof c)
generalize solver φs' (program, φs, _) = do
  let φs'' = foldl' (<>) φs φs'
  π ← lower (proofToNFA solver φs'')
  when debug do
    putStrLn "[debug] ~~~ New Assertions ~~~"
    for_ (OrdSet.difference φs'' φs) \φ → do
      putStr "        "
      prettyPrint φ
  return (program, φs'', π)

proofToNFA ∷ (Container c ([Tag], Stmt), ?config ∷ Config) ⇒ Solver' → Assertions → NFAM IO (IMap c)
proofToNFA (Solver' {..}) π = reify πlist \π'@(root:final:_) →
  let stmts = universe

      isIndependent φ (lookup → (tag₁, stmt₁)) (lookup → (tag₂, stmt₂))
        | conflicts tag₁ tag₂ = return False
        | otherwise = isIndep' φ stmt₁ stmt₂

      next φ = do
        indeps ← mapM (\stmt → (stmt,) <$> filterM (isIndependent (lookup φ) stmt) stmts) stmts
        δ      ← mapM (\s → (s,) <$> filterM (isTriple' (lookup φ) (snd (lookup s)) . lookup) π') stmts
        let indeps' = fmap Set.fromList (Map.fromList indeps)
            δ' = map (fmap Set.fromList) (filter (not . null . snd) δ)
        when (debug && False) do
          printf "[debug] ~~~ Dependence Relation for %s ~~~\n" (pretty (toSExpr (lookup φ)))
          for_ indeps \(s, ss) → do
            putStr "        "
            prettyPrint (snd (lookup s))
            for_ ss \s' → do
              putStr "          "
              prettyPrint (snd (lookup s'))
        return (NFA.Edge (IMap indeps' (Map.fromList δ')) (φ == final))

  in UnfoldM next root
  where πlist = true : false : OrdSet.toList (OrdSet.delete true (OrdSet.delete false π))
