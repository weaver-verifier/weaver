{-# LANGUAGE
    BlockArguments,
    DeriveTraversable,
    FlexibleContexts,
    GADTs,
    ImplicitParams,
    LambdaCase,
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

module Main (main) where

import           Prelude hiding (lookup, putStrLn, readFile)
import           Control.Exception.Base (evaluate)
import           Control.Monad (when)
import           Control.Monad.Except (runExceptT, throwError)
import           Control.Monad.IO.Class (MonadIO (..))
import           Data.Automata.Regex (Regex, canonical, toDFA)
import           Data.Finite.Container (Index, lookup)
import           Data.Foldable (for_)
import           Data.IORef (modifyIORef', newIORef, readIORef, writeIORef)
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map as OrdMap
import qualified Data.Set as OrdSet
import           Data.Text (Text, pack)
import           Data.Text.IO (putStrLn, readFile)
import           Data.Void (Void)
import           Language.SMT.Expr (Expr, true, false)
import           Language.SMT.SExpr (SExpr, parseAll, prettyPrint)
import           Language.SMT.Solver (Solver, newSolver)
import           Numeric.Natural (Natural)
import           System.Exit (exitFailure)
import           System.IO (hFlush, stdout)
import           System.Clock (Clock (..), diffTimeSpec, getTime, toNanoSecs)
import           Text.Printf (printf)
import           Weaver.Algorithm (Assertions, Algorithm (..), Interface (..), Solver' (..), Config, debug, semi)
import           Weaver.Program (Program (..), compile)
import           Weaver.Stmt (V, Stmt (..), prove, isTriple, isIndep)
import           Weaver.Bound (Bound (..), bounded)
import           Weaver.Options (Options (..), parseOptions)

main ∷ IO ()
main = do
  Options filepath algorithm backend script config bound iters ← parseOptions
  file    ← readFile filepath
  sexprs  ← parseProgram file
  program ← compileProgram sexprs
  solver  ← newSolver (backend script)
  let ?config = config
  result  ← time "Total time" (verifyProgram bound iters solver algorithm program)
  case result of
    Nothing → putStrLn "SUCCESS"
    Just xs → do mapM_ prettyPrint xs
                 putStrLn "FAILURE"

parseProgram ∷ Text → IO [SExpr Void]
parseProgram text =
  case parseAll text of
    Right xs → return xs
    Left err → do
      putStrLn err
      exitFailure

compileProgram ∷ [SExpr Void] → IO Program
compileProgram sexprs = do
  result ← runExceptT (compile sexprs)
  case result of
    Right pair → return pair
    Left err → liftIO do
      putStrLn err
      exitFailure

time ∷ String → IO a → IO a
time label action = do
  start₁ ← getTime Monotonic
  start₂ ← getTime ProcessCPUTime
  result ← action
  end₁   ← getTime Monotonic
  end₂   ← getTime ProcessCPUTime
  printf "%s: [real] %0.6fs [process] %0.6fs\n"
    label
    (fromIntegral (toNanoSecs (diffTimeSpec start₁ end₁)) / 1000000000 ∷ Double)
    (fromIntegral (toNanoSecs (diffTimeSpec start₂ end₂)) / 1000000000 ∷ Double)
  hFlush stdout
  return result

-- partitionProgressSetsCheck ∷ ∀c. Container c ([Tag], Stmt) ⇒ Map (Index c) (Set (Index c)) → DFA (Map (Index c)) → Cex c
-- partitionProgressSetsCheck deps (Unfold next (root ∷ q)) =
--   fromMaybe mempty (foldCut go₁ Nothing isJust (unfold go₂ (root, Set.empty))) where
--     go₁ ∷ (r → Maybe (Cex c)) → Lists' (Index c) r → Maybe (Cex c)
--     go₁ k (Lists' xs) = do
--       ys ← traverse (asum . map (traverse k)) xs
--       case ys of
--         [] → return Nil
--         _  → return (Cons (Map.fromListWith (<>) ys))

--     go₂ ∷ (q, Set (Index c)) → Lists' (Index c) (q, Set (Index c))
--     go₂ (q, s) =
--       case next q of
--         DFA.Edge _ True → Lists' []
--         DFA.Edge δ False → Lists' do
--           part ← map Set.fromList (subsequences (keys δ))
--           return do
--             (a, q') ← toKeyedList δ
--             guard (not (Set.member a s))
--             let orderₐ = if Set.member a part then Set.empty else part
--                 depsₐ = index deps a
--             return (a, (q', Set.difference (Set.union s orderₐ) depsₐ))

-- partitionSetsCheck ∷ ∀c. Container c ([Tag], Stmt) ⇒ Map (Index c) (Set (Index c)) → DFA (Map (Index c)) → Bool
-- partitionSetsCheck deps (Unfold next (root ∷ q)) =
--     not (foldCut go₁ False id (unfold go₂ (root, Set.empty))) where
--   go₁ ∷ (r → Bool) → Lists r → Bool
--   go₁ k (Lists xs) = all (any k) xs

--   go₂ ∷ (q, Set (Index c)) → Lists (q, Set (Index c))
--   go₂ (q, s) =
--     case next q of
--       DFA.Edge _ True → Lists []
--       DFA.Edge δ False → Lists do
--         part ← map Set.fromList (subsequences (keys δ))
--         return do
--           (a, q') ← toKeyedList δ
--           guard (not (Set.member a s))
--           let orderₐ = if Set.member a part then Set.empty else part
--               depsₐ = index deps a
--           return (q', Set.difference (Set.union s orderₐ) depsₐ)

-- totalOrderCheck ∷ ∀c. Container c ([Tag], Stmt) ⇒ Map (Index c) (Set (Index c)) → DFA (Map (Index c)) → Bool
-- totalOrderCheck deps = AC.isEmpty . foldCut go AC.empty (not . AC.isEmpty) where
--   go ∷ (r → Antichain (Index c)) → DFA.Edge (Map (Index c)) r → Antichain (Index c)
--   go _ (DFA.Edge _ True) = AC.universe
--   go k (DFA.Edge δ False) = AC.intersections do
--     order ← permutations (keys δ)
--     return . AC.unions $ do
--       (a, q) ← toKeyedList δ
--       pₘₐₓ ← AC.toList (k q)
--       let orderₐ = Set.fromList (dropWhile (/= a) order)
--           depsₐ = index deps a
--       return $
--         if Set.isSubsetOf (Set.difference orderₐ depsₐ) pₘₐₓ
--         then AC.singleton (Set.delete a (Set.unions [pₘₐₓ, orderₐ, depsₐ]))
--         else AC.empty

verifyProgram ∷ (?config ∷ Config) ⇒ Bound → Natural → Solver V → Algorithm → Program → IO (Maybe [Stmt])
verifyProgram bound iters solver (Algorithm algorithm) (Program asserts (regex ∷ Regex (Index c))) = do
  isTripleCache ← newIORef OrdMap.empty
  isIndepCache  ← newIORef OrdMap.empty

  let isTriple' ∷ Expr V Bool → Stmt → Expr V Bool → IO Bool
      isTriple' φ s ψ = do
        isTripleCache₀ ← readIORef isTripleCache
        let key = (φ, s, ψ)
        case OrdMap.lookup key isTripleCache₀ of
          Just result → return result
          Nothing → do
            result ← isTriple solver φ (s) ψ
            writeIORef isTripleCache (OrdMap.insert key result isTripleCache₀)
            return result

      isIndep' ∷ Expr V Bool → Stmt → Stmt → IO Bool
      isIndep' φ s₁ s₂ = do
        isIndepCache₀ ← readIORef isIndepCache
        let key = (φ, s₁, s₂)
        case OrdMap.lookup key isIndepCache₀ of
          Just result → return result
          Nothing → do
            result ← isIndep solver semi φ s₁ s₂
            writeIORef isIndepCache (OrdMap.insert key result isIndepCache₀)
            return result

      program = toDFA (canonical regex)

  Interface initialize size check generalize ← return (algorithm (Solver' {..}) program)

  let loop π n = do
        when (iters /= 0 && n > iters) (error "Maximum iterations exceeded")

        putStrLn "------------------------------"
        printf "Iteration %d\n" n
        printf "Current proof size: %d\n" (size π)
        hFlush stdout

        bounded bound <$> time "Searching for counter-example" (evaluate (check π)) >>= \case
          []   → return (Nothing, n)
          cexs → do
            printf "Found %d counter-examples\n" (length cexs)
            when debug do
              for_ (zip cexs [0..]) \(cex, i ∷ Int) → do
                putStrLn ("[debug] ~~~ Counter-Example " <> pack (show i) <> " ~~~")
                for_ cex \x → do
                  putStr "        "
                  prettyPrint (snd (lookup x))

            time "Generating interpolants" (interpolate cexs) >>= \case
              Left bad → return (Just (map (snd . lookup) bad), n)
              Right φs → do
                π' ← time "Generalizing proof" (generalize φs π)
                loop π' (n + 1)

      interpolate ∷ [[Index c]] → IO (Either [Index c] [Assertions])
      interpolate = runExceptT . traverse \cex → do
        result ← prove solver (NonEmpty.fromList (map (snd . lookup) cex))
        case result of
          Nothing → throwError cex
          Just π' → liftIO do
            for_ (zip3 (true:π') cex (π' ++ [false])) \(φ, x, ψ) →
              modifyIORef' isTripleCache (OrdMap.insert (φ, snd (lookup x), ψ) True)
            return (OrdSet.fromList π')

  π ← time "Initializing" (initialize (OrdSet.fromList asserts))

  (result, n) ← loop π 1
  printf "Iterations: %d\n" n
  hFlush stdout
  return result
