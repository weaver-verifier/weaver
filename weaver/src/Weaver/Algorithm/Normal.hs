{-# LANGUAGE
    BlockArguments,
    FlexibleContexts,
    ImplicitParams,
    MonoLocalBinds,
    TupleSections,
    UnicodeSyntax
  #-}

module Weaver.Algorithm.Normal where

import           Control.Monad (when)
import           Data.Automata.DFA (DFA, approximate, difference, find, member)
import           Data.Automata.NFA (NFA)
import qualified Data.Automata.NFA as NFA
import           Data.Automata.Graph (lower, optimize, vertices)
import qualified Data.Automata.Regex as Regex
import           Data.Finite.Container (Container, Index)
import           Data.Finite.Small.Map (Map)
import           Data.Foldable (for_, foldl')
import           Data.Set ((\\), fromDistinctAscList, toAscList)
import           Language.SMT.SExpr (prettyPrint)
import           Weaver.Algorithm (Algorithm (..), Assertions, Solver' (..), Interface (..), proofToNFA)
import           Weaver.Config (Config, debug)
import           Weaver.Counterexample (Counterexample (..), singleton)
import           Weaver.Program (Tag)
import           Weaver.Stmt (Stmt)

algorithm ∷ Algorithm
algorithm = Algorithm \solver program → Interface
  (initialize solver)
  size
  (check (Regex.toDFA program))
  (generalize solver)
  (display . fst)
  (shrink solver)

type Proof c = (Assertions, NFA (Map (Index c)))

initialize ∷ Container c ([Tag], Stmt) ⇒ Solver' → Assertions → IO (Proof c)
initialize solver φs = (φs,) <$> lower (proofToNFA solver φs)

size ∷ Proof c → Int
size = vertices . snd

check ∷ Container c a ⇒ DFA (Map (Index c)) → Proof c -> Counterexample c
check programDFA (_, πNFA) =
  let πDFA = NFA.toDFA πNFA
      diff = difference programDFA πDFA
      opt  = optimize (approximate diff)
  in case find opt of
       Nothing → mempty
       Just xs | xs `member` πDFA → error "xs ∈ πDFA!"
       Just xs → singleton xs

generalize ∷ (Container c ([Tag], Stmt), ?config ∷ Config) ⇒ Solver' → [Assertions] → Proof c → IO (Proof c)
generalize solver φs' (φs, _) = do
  let φs'' = foldl' (<>) φs φs'
  when debug do
    putStrLn "[debug] ~~~ New Assertions ~~~"
    for_ (φs'' \\ φs) \φ → do
    -- for_ φs'' \φ → do
      putStr "        "
      prettyPrint φ
  initialize solver φs''

display ∷ (?config ∷ Config) ⇒ Assertions → IO ()
display φs = when debug do
  putStrLn "[debug] ~~~ Final Proof ~~~"
  mapM_ (\φ → putStr "        " >> prettyPrint φ) φs

shrink ∷ Container c ([Tag], Stmt) ⇒ Solver' → Proof c → [IO (Proof c)]
shrink solver (φs, _) = map (initialize solver . fromDistinctAscList) (deletes (toAscList φs))
  where deletes [] = []
        deletes (x:xs) = xs : map (x:) (deletes xs)
