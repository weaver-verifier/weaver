{-# LANGUAGE
    BlockArguments,
    FlexibleContexts,
    ImplicitParams,
    MonoLocalBinds,
    TupleSections,
    UnicodeSyntax
  #-}

module Weaver.Algorithm.Normal where

import Control.Monad (when)
import Data.Automata.DFA (DFA, approximate, difference, find, member)
import Data.Automata.NFA (NFA, toDFA)
import Data.Automata.Graph (lower, optimize, vertices)
import Data.Finite.Container (Container, Index)
import Data.Finite.Small.Map (Map)
import Data.Foldable (for_, foldl')
import Data.Set ((\\))
import Language.SMT.SExpr (prettyPrint)
import Weaver.Algorithm (Algorithm (..), Assertions, DebugMode (..), Solver' (..), Interface (..), proofToNFA)
import Weaver.Counterexample (Counterexample (..), singleton)
import Weaver.Program (Tag)
import Weaver.Stmt (Stmt)

algorithm ∷ Algorithm
algorithm = Algorithm \solver program → Interface
  (initialize solver)
  size
  (check program)
  (generalize solver)

type Proof c = (Assertions, NFA (Map (Index c)))

initialize ∷ Container c ([Tag], Stmt) ⇒ Solver' → Assertions → IO (Proof c)
initialize solver φs = (φs,) <$> lower (proofToNFA solver φs)

size ∷ Proof c → Int
size = vertices . snd

check ∷ Container c a ⇒ DFA (Map (Index c)) → Proof c -> Counterexample c
check programDFA (_, πNFA) =
  let πDFA = toDFA πNFA
      diff = difference programDFA πDFA
      opt  = optimize (approximate diff)
  in case find opt of
       Nothing → mempty
       Just xs | xs `member` πDFA → error "xs ∈ πDFA!"
       Just xs → singleton xs

generalize ∷ (Container c ([Tag], Stmt), ?debug ∷ DebugMode) ⇒ Solver' → [Assertions] → Proof c → IO (Proof c)
generalize solver φs' (φs, _) = do
  let φs'' = foldl' (<>) φs φs'
  when (?debug == Debug) do
    putStrLn "[debug] ~~~ New Assertions ~~~"
    for_ (φs'' \\ φs) \φ → do
    -- for_ φs'' \φ → do
      putStr "        "
      prettyPrint φ
  initialize solver φs''
