{-# LANGUAGE
    BlockArguments,
    FlexibleContexts,
    MonoLocalBinds,
    TupleSections,
    UnicodeSyntax
  #-}

module Weaver.Algorithm.NormalTrace where

import Data.Automata.DFA (DFA, difference, find)
import Data.Automata.NFA (toDFA)
import Data.Automata.Graph (lower, optimize, vertices)
import Data.Finite.Container (Container, Index)
import Data.Finite.Small.Map (Map)
import Data.Foldable (foldl')
import Weaver.Algorithm (Algorithm (..), Assertions, Solver' (..), Interface (..), proofToNFA)
import Weaver.Counterexample (Counterexample (..), singleton)
import Weaver.Program (Tag)
import Weaver.Stmt (Stmt)

algorithm ∷ Algorithm
algorithm = Algorithm \solver program → Interface
  (initialize solver program)
  size
  check
  (generalize solver)
  (const (return ()))

type Proof c = DFA (Map (Index c))

initialize ∷ Container c ([Tag], Stmt) ⇒ Solver' → DFA (Map (Index c)) → Assertions → IO (Proof c)
initialize solver program φs =
  optimize . difference program . toDFA <$>
  lower (proofToNFA solver φs)

size ∷ Proof c → Int
size = vertices

check ∷ Container c a ⇒ Proof c -> Counterexample c
check = maybe mempty singleton . find

generalize ∷ Container c ([Tag], Stmt) ⇒ Solver' → [Assertions] → Proof c → IO (Proof c)
generalize solver φs π = do
  φs' ← mapM (fmap toDFA . lower . proofToNFA solver) φs
  return (optimize (foldl' difference π φs'))
