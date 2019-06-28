{-# LANGUAGE
    BlockArguments,
    DeriveTraversable,
    FlexibleContexts,
    GADTs,
    ImplicitParams,
    LambdaCase,
    OverloadedLists,
    OverloadedStrings,
    PatternSynonyms,
    RankNTypes,
    RecordWildCards,
    ScopedTypeVariables,
    TupleSections,
    TypeOperators,
    UnicodeSyntax,
    ViewPatterns
  #-}

module Weaver.Algorithm where

import           Prelude hiding (lookup, putStrLn, readFile)
import           Control.Monad (filterM)
import           Data.Automata.Graph (GraphM (..))
import           Data.Automata.DFA (DFA)
import           Data.Automata.NFA (NFAM, Edge (..))
import           Data.Finite.Class (universe)
import           Data.Finite.Container (Container, Index, lookup, reify)
import qualified Data.Finite.Set as Set
import           Data.Finite.Small.Map (Map)
import qualified Data.Finite.Small.Map as Map
import           Data.Set (Set, (\\), toList)
import           Language.SMT.Expr (Expr, true, false)
import           Weaver.Program (Tag)
import           Weaver.Stmt (V, Stmt)
import           Weaver.Config
import           Weaver.Counterexample

type Assertions = Set (Expr V Bool)

data Solver' = Solver'
  { isTriple' ∷ Expr V Bool → Stmt → Expr V Bool → IO Bool
  , isIndep'  ∷ Expr V Bool → Stmt → Stmt → IO Bool
  }

newtype Algorithm = Algorithm (∀c.
  (Container c ([Tag], Stmt), ?config ∷ Config) ⇒
  Solver' →
  DFA (Map (Index c)) →
  Interface c)

data Interface c = ∀π. Interface
  (Assertions → IO π)       -- Initialize
  (π → Int)                 -- Size
  (π → Counterexample c)    -- Check
  ([Assertions] → π → IO π) -- Generalize

proofToNFA ∷ Container c ([Tag], Stmt) ⇒ Solver' → Assertions → NFAM IO (Map (Index c))
proofToNFA (Solver' {..}) π = reify πlist \π'@(root:final:_) →
  let stmts  = universe
      next φ = do
        δ ← mapM (\s → (s,) <$> filterM (isTriple' (lookup φ) (snd (lookup s)) . lookup) π') stmts
        let δ' = map (fmap Set.fromList) (filter (not . null . snd) δ)
        return (Edge (Map.fromList δ') (φ == final))
  in UnfoldM next root
  where πlist = true : false : toList (π \\ [true, false])
