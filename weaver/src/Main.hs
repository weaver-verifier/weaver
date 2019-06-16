{-# LANGUAGE
    BlockArguments,
    DeriveTraversable,
    FlexibleContexts,
    GADTs,
    LambdaCase,
    OverloadedStrings,
    PatternSynonyms,
    ScopedTypeVariables,
    TupleSections,
    TypeOperators,
    UnicodeSyntax,
    ViewPatterns
  #-}

module Main (main) where

import           Prelude hiding (lookup, putStrLn, readFile)
import           Control.Exception.Base (evaluate)
import           Control.Monad (filterM, guard, when)
import           Control.Monad.Except (runExceptT)
import           Control.Monad.State (evalState, get, modify')
import           Control.Monad.IO.Class (MonadIO (..))
import           Data.Automata.DFA (DFA, approximate, difference, find)
import qualified Data.Automata.DFA as DFA
import           Data.Automata.Graph (pattern Unfold, GraphM (..), lower, foldCut, optimize, unfold, vertices)
import           Data.Automata.NFA (NFA, NFAM, Edge (..))
import qualified Data.Automata.NFA as NFA
import           Data.Automata.Regex (Regex, canonical, toDFA)
import           Data.Finite.Class (Finitary)
import           Data.Finite.Container (Container, Index, lookup, reify)
import           Data.Finite.Set.Antichain (Antichain)
import qualified Data.Finite.Set.Antichain as AC
import           Data.Finite.Set.AntiMap (AntiMap)
import qualified Data.Finite.Set.AntiMap as AM
import           Data.Finite.Set (Set, union)
import qualified Data.Finite.Set as Set
import           Data.Finite.Small (Small)
import           Data.Finite.Small.Map (Map, keys, fromList, fromListWith)
import qualified Data.Finite.Small.Map as Map
import           Data.Foldable (asum, for_, toList)
import           Data.Functor.Compose (Compose (..))
import           Data.Functor.Product (Product (..))
import           Data.Function (on)
import           Data.IORef (modifyIORef', newIORef, readIORef, writeIORef)
import           Data.List (permutations, sortBy, subsequences)
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map as OrdMap
import           Data.Maybe (fromMaybe, isJust)
import qualified Data.Set as OrdSet
import           Data.Key (index, toKeyedList)
import           Data.Text (Text, pack)
import           Data.Text.IO (putStrLn, readFile)
import           Data.Traversable (for)
import           Data.Void (Void)
import           Language.SMT.Expr (Expr, true, false)
import           Language.SMT.SExpr (SExpr, parseAll, prettyPrint)
import           Language.SMT.Solver (Solver, newSolver)
import           Numeric.Natural (Natural)
import           System.Exit (exitFailure)
import           System.IO (hFlush, stdout)
import           System.Clock (Clock (..), diffTimeSpec, getTime, toNanoSecs)
import           Text.Printf (printf)
import           Weaver.Program (Tag, Program (..), compareIndep, compile, conflicts)
import           Weaver.Stmt (V, Stmt (..), prove, isSwappable, isTriple, isIndep)
import           Weaver.Options (Options (..), Method (..), DebugMode (..), TestMode (..), Bound (..), parseOptions)

main ∷ IO ()
main = do
  Options filepath method backend debug test bound iters ← parseOptions
  file    ← readFile filepath
  sexprs  ← parseProgram file
  program ← compileProgram sexprs
  solver  ← newSolver backend
  result  ← verifyProgram method debug test bound iters solver program
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

data Cex c = Nil | Cons (Map (Index c) (Cex c))

instance Semigroup (Cex c) where
  Nil <> _ = Nil
  _ <> Nil = Nil
  Cons m₁ <> Cons m₂ = Cons (Map.unionWith (<>) m₁ m₂)

instance Monoid (Cex c) where
  mempty = Cons Map.empty

instance Eq (Cex c) where
  _ == _ = True

singleton ∷ Container c a ⇒ [Index c] → Cex c
singleton [] = Nil
singleton (x:xs) = extend x (singleton xs)

getCex ∷ Container c a ⇒ Cex c → [[Index c]]
getCex Nil = [[]]
getCex (Cons m) = do
  (a, m') ← toKeyedList m
  x ← getCex m'
  return (a:x)

extend ∷ Container c a ⇒ Index c → Cex c → Cex c
extend x c = Cons (Map.singleton x c)

newtype Lists a = Lists [[a]]
  deriving (Foldable, Functor, Traversable)

data Lists' k v = Lists' [[(k, v)]]
  deriving (Foldable, Functor, Traversable)

type Proof = OrdSet.Set (Expr V Bool)

type (:*:) = Product
type (:.:) = Compose

verifyProgram ∷ Method → DebugMode → TestMode → Bound → Natural → Solver V → Program → IO (Maybe [Stmt])
verifyProgram method debug test bound iters solver (Program asserts (regex ∷ Regex (Index c))) = do
  isTripleCache ← newIORef OrdMap.empty
  isIndepCache  ← newIORef OrdMap.empty

  let stmts ∷ [Index c]
      stmts = toList regex

      isDependent ∷ Index c → Index c → IO Bool
      isDependent (lookup → (tag₁, stmt₁)) (lookup → (tag₂, stmt₂))
        | conflicts tag₁ tag₂ = return True
        | otherwise = not <$> isSwappable solver stmt₁ stmt₂

      toRel ∷ (Small k, Finitary v) ⇒ [(k, v)] → Map k (Set v)
      toRel xs = fromListWith union (map (fmap Set.singleton) xs)

  prompt "Computing dependence relation: "
  deps ← time (toRel <$> filterM (uncurry isDependent) ((,) <$> stmts <*> stmts))

  let isTriple' ∷ Container s (Expr V Bool) ⇒ Index s → Index c → Index s → IO Bool
      isTriple' φ s ψ = do
        isTripleCache₀ ← readIORef isTripleCache
        let key = (lookup φ, snd (lookup s), lookup ψ)
        case OrdMap.lookup key isTripleCache₀ of
          Just result → return result
          Nothing → do
            result ← isTriple solver (lookup φ) (snd (lookup s)) (lookup ψ)
            writeIORef isTripleCache (OrdMap.insert key result isTripleCache₀)
            return result

      isIndep' ∷ Container s (Expr V Bool) ⇒ Index s → Index c → Index c → IO Bool
      isIndep' φ s₁ s₂ = do
        isIndepCache₀ ← readIORef isIndepCache
        let key = (lookup φ, snd (lookup s₁), snd (lookup s₂))
        case OrdMap.lookup key isIndepCache₀ of
          Just result → return result
          Nothing → do
            result ← isIndep solver (lookup φ) (snd (lookup s₁)) (snd (lookup s₂))
            writeIORef isIndepCache (OrdMap.insert key result isIndepCache₀)
            return result

      proof ∷ Proof → NFAM IO (Map (Index c))
      proof π = reify (toList π) \π' →
        let unreify = (OrdMap.fromList (zip (toList π) π') OrdMap.!)
            true'  = unreify true
            false' = unreify false
            root = true'
            next φ = do
              δ ← filterM (\(s, ψ) → isTriple' φ s ψ) ((,) <$> stmts <*> π')
              return (Edge (toRel δ) (φ == false'))
        in UnfoldM next root

      indepProof ∷ Proof → NFAM IO (Map (Index c) :*: (Map (Index c) :.: Map (Index c)))
      indepProof π = reify (toList π) \π' →
        let unreify = (OrdMap.fromList (zip (toList π) π') OrdMap.!)
            true'  = unreify true
            false' = unreify false
            root = true'
            next φ = do
              δ₁ ← filterM (\(s,  ψ)  → isTriple' φ s  ψ)  ((,) <$> stmts <*> π')
              δ₂ ← mapM (\stmt → (stmt,) <$> filterM (fmap not . isIndep' φ stmt) stmts) stmts
              let δ₃ = fmap (fromList . map (, Set.singleton false')) (fromList δ₂)
              return (Edge (Pair (toRel δ₁) (Compose δ₃)) (φ == false'))
        in UnfoldM next root

      programDFA ∷ DFA (Map (Index c))
      programDFA = toDFA (canonical regex)

      indepProgramDFA ∷ DFA (Map (Index c) :*: (Map (Index c) :.: Map (Index c)))
      indepProgramDFA = addIndeps programDFA

      addIndeps ∷ DFA (Map (Index c)) → DFA (Map (Index c) :*: (Map (Index c) :.: Map (Index c)))
      addIndeps (Unfold next root) = Unfold next' root'
        where root' = Just root
              next' Nothing = DFA.Edge (Pair Map.empty (Compose Map.empty)) True
              next' (Just (next → DFA.Edge δ b)) =
                let ks  = keys δ
                    ps  = fromList (map (\stmt → (stmt, filter (not . confl stmt) ks)) ks)
                    ps' = fmap (fromList . map (, Nothing)) ps
                    confl (lookup → (x, _)) (lookup → (y, _)) = conflicts x y
                in DFA.Edge (Pair (fmap Just δ) (Compose ps')) b

      check ∷ NFA (Map (Index c)) → Cex c
      check πNFA =
        case method of
          FloydHoare            → ce
          PartitionProgress     → partitionProgressCheck deps diff
          PartitionProgressSets → partitionProgressSetsCheck deps diff
          Partition             → if partitionCheck deps diff then mempty else ce
          PartitionSets         → if partitionSetsCheck deps diff then mempty else ce
          TotalOrder            → if totalOrderCheck deps diff then mempty else ce
        where ce = maybe mempty singleton (find diff)
              diff = optimize (approximate (difference programDFA πDFA))
              πDFA = NFA.toDFA πNFA

      interpolate ∷ [[Index c]] → Proof → IO (Either [Index c] Proof)
      interpolate [] π = return (Right π)
      interpolate (cex:cexs) π = do
        result ← prove solver (NonEmpty.fromList (map (snd . lookup) cex))
        case result of
          Nothing → return (Left cex)
          Just π' → do
            for_ (zip3 (true:π') cex (π' ++ [false])) \(φ, x, ψ) →
              modifyIORef' isTripleCache (OrdMap.insert (φ, snd (lookup x), ψ) True)
            interpolate cexs (OrdSet.union π (OrdSet.fromList π'))

      loop ∷ Proof → Natural → IO (Maybe [Stmt], Natural)
      loop π n = do
        when (iters /= 0 && n > iters) (error "Maximum iterations exceeded")

        putStrLn "------------------------------"
        printf "Iteration %d\n" n
        printf "Using %d assertions\n" (length π)
        prompt "Constructing proof: "
        πNFA ← time (lower (proof π))

        when (debug == Debug) do
          printf "[debug] Proof DFA has %d reachable states\n"
            (vertices (optimize (NFA.toDFA πNFA)) ∷ Natural)

        prompt "Searching for counter-example: "
        bounded bound <$> time (evaluate (check πNFA)) >>= \case
          [] → do
            when (debug == Debug) do
              putStrLn "[debug] ~~~ Final Proof ~~~"
              for_ π \φ → do
                putStr "        "
                prettyPrint φ
            when (test == Test) do
              let diff = optimize (approximate (difference programDFA πDFA))
                  πDFA = NFA.toDFA πNFA
              prompt "[test] Optimized   Check: "
              _ ← time (evaluate (partitionCheck deps diff))
              prompt "[test] Unoptimized Check: "
              _ ← time (evaluate (partitionSetsCheck deps diff))
              return ()
            return (Nothing, n)
          cexs → do
            printf "Found %d counter-examples\n" (length cexs)
            when (debug == Debug) do
              for_ (zip cexs [0..]) \(cex, i ∷ Int) → do
                putStrLn ("[debug] ~~~ Counter-Example " <> pack (show i) <> " ~~~")
                for_ cex \x → do
                  putStr "        "
                  prettyPrint (snd (lookup x))

            prompt "Generating interpolants: "
            time (interpolate cexs π) >>= \case
              Left bad → return (Just (map (snd . lookup) bad), n)
              Right π' → do
                when (debug == Debug) do
                  putStrLn "[debug] ~~~ New Assertions ~~~"
                  for_ (OrdSet.difference π' π) \φ → do
                    putStr "        "
                    prettyPrint φ
                loop π' (n + 1)

  (result, n) ← time (loop (OrdSet.fromList (true : false : asserts)) 1)
  putStrLn ("Iterations: " <> pack (show n))
  return result

prompt ∷ String → IO ()
prompt text = putStr text >> hFlush stdout

time ∷ IO a → IO a
time action = do
  start₁ ← getTime Monotonic
  start₂ ← getTime ProcessCPUTime
  result ← action
  end₁   ← getTime Monotonic
  end₂   ← getTime ProcessCPUTime
  printf "[real] %0.6fs [process] %0.6fs\n"
    (fromIntegral (toNanoSecs (diffTimeSpec start₁ end₁)) / 1000000000 ∷ Double)
    (fromIntegral (toNanoSecs (diffTimeSpec start₂ end₂)) / 1000000000 ∷ Double)
  return result

partitionProgressCheck ∷ ∀c. Container c ([Tag], Stmt) ⇒ Map (Index c) (Set (Index c)) → DFA (Map (Index c)) → Cex c
partitionProgressCheck deps = fromMaybe mempty
                            . AM.lookup Set.empty
                            . foldCut go AM.empty (not . AM.isEmpty) where
  go ∷ (r → AntiMap (Index c) (Cex c)) → DFA.Edge (Map (Index c)) r → AntiMap (Index c) (Cex c)
  go _ (DFA.Edge _ True)  = AM.universe Nil
  go k (DFA.Edge δ False) = AM.intersectionsWith (<>) mempty do
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

partitionProgressSetsCheck ∷ ∀c. Container c ([Tag], Stmt) ⇒ Map (Index c) (Set (Index c)) → DFA (Map (Index c)) → Cex c
partitionProgressSetsCheck deps (Unfold next (root ∷ q)) =
  fromMaybe mempty (foldCut go₁ Nothing isJust (unfold go₂ (root, Set.empty))) where
    go₁ ∷ (r → Maybe (Cex c)) → Lists' (Index c) r → Maybe (Cex c)
    go₁ k (Lists' xs) = do
      ys ← traverse (asum . map (traverse k)) xs
      case ys of
        [] → return Nil
        _  → return (Cons (Map.fromListWith (<>) ys))

    go₂ ∷ (q, Set (Index c)) → Lists' (Index c) (q, Set (Index c))
    go₂ (q, s) =
      case next q of
        DFA.Edge _ True → Lists' []
        DFA.Edge δ False → Lists' do
          part ← map Set.fromList (subsequences (keys δ))
          return do
            (a, q') ← toKeyedList δ
            guard (not (Set.member a s))
            let orderₐ = if Set.member a part then Set.empty else part
                depsₐ = index deps a
            return (a, (q', Set.difference (Set.union s orderₐ) depsₐ))

partitionCheck ∷ ∀c. Container c ([Tag], Stmt) ⇒ Map (Index c) (Set (Index c)) → DFA (Map (Index c)) → Bool
partitionCheck deps = AC.isEmpty . foldCut go AC.empty (not . AC.isEmpty) where
  go ∷ (r → Antichain (Index c)) → DFA.Edge (Map (Index c)) r → Antichain (Index c)
  go _ (DFA.Edge _ True) = AC.universe
  go k (DFA.Edge δ False) = AC.intersections do
    part ← map Set.fromList (subsequences (keys δ))
    return . AC.unions $ do
      (a, q) ← toKeyedList δ
      pₘₐₓ ← AC.toList (k q)
      let orderₐ = if Set.member a part then Set.empty else part
          depsₐ = index deps a
      return $
        if Set.isSubsetOf (Set.difference orderₐ depsₐ) pₘₐₓ
        then AC.singleton (Set.delete a (Set.unions [pₘₐₓ, orderₐ, depsₐ]))
        else AC.empty

partitionSetsCheck ∷ ∀c. Container c ([Tag], Stmt) ⇒ Map (Index c) (Set (Index c)) → DFA (Map (Index c)) → Bool
partitionSetsCheck deps (Unfold next (root ∷ q)) =
    not (foldCut go₁ False id (unfold go₂ (root, Set.empty))) where
  go₁ ∷ (r → Bool) → Lists r → Bool
  go₁ k (Lists xs) = all (any k) xs

  go₂ ∷ (q, Set (Index c)) → Lists (q, Set (Index c))
  go₂ (q, s) =
    case next q of
      DFA.Edge _ True → Lists []
      DFA.Edge δ False → Lists do
        part ← map Set.fromList (subsequences (keys δ))
        return do
          (a, q') ← toKeyedList δ
          guard (not (Set.member a s))
          let orderₐ = if Set.member a part then Set.empty else part
              depsₐ = index deps a
          return (q', Set.difference (Set.union s orderₐ) depsₐ)

totalOrderCheck ∷ ∀c. Container c ([Tag], Stmt) ⇒ Map (Index c) (Set (Index c)) → DFA (Map (Index c)) → Bool
totalOrderCheck deps = AC.isEmpty . foldCut go AC.empty (not . AC.isEmpty) where
  go ∷ (r → Antichain (Index c)) → DFA.Edge (Map (Index c)) r → Antichain (Index c)
  go _ (DFA.Edge _ True) = AC.universe
  go k (DFA.Edge δ False) = AC.intersections do
    order ← permutations (keys δ)
    return . AC.unions $ do
      (a, q) ← toKeyedList δ
      pₘₐₓ ← AC.toList (k q)
      let orderₐ = Set.fromList (dropWhile (/= a) order)
          depsₐ = index deps a
      return $
        if Set.isSubsetOf (Set.difference orderₐ depsₐ) pₘₐₓ
        then AC.singleton (Set.delete a (Set.unions [pₘₐₓ, orderₐ, depsₐ]))
        else AC.empty

bounded ∷ Container c ([Tag], a) ⇒ Bound → Cex c → [[Index c]]
bounded NoBound          = getCex
bounded (BoundLeft n)    = selectLeft    (fromIntegral n)
bounded (BoundRight n)   = selectRight   (fromIntegral n)
bounded (BoundMiddle n)  = selectMiddle  (fromIntegral n) . getCex
bounded (BoundAzadeh n)  = selectAzadeh  (fromIntegral n) . getCex
bounded (BoundUniform n) = selectUniform (fromIntegral n) . getCex
bounded BoundRoundRobin  = selectRoundRobin

selectLeft ∷ Container c a ⇒ Int → Cex c → [[Index c]]
selectLeft n cex = evalState (go cex) 0
  where go Nil = do
          modify' (+ 1)
          return [[]]
        go (Cons m) =
          concat <$> for (toKeyedList m) \(k, v) → do
            i ← get
            if i < n then
              map (k:) <$> go v
            else
              return []

selectRight ∷ Container c a ⇒ Int → Cex c → [[Index c]]
selectRight n cex = evalState (go cex) 0
  where go Nil = do
          modify' (+ 1)
          return [[]]
        go (Cons m) =
          concat <$> for (reverse (toKeyedList m)) \(k, v) → do
            i ← get
            if i < n then
              map (k:) <$> go v
            else
              return []

selectRoundRobin ∷ Container c ([Tag], a) ⇒ Cex c → [[Index c]]
selectRoundRobin = go []
  where go _ Nil = [[]]
        go x (Cons m) =
            case dropWhile ((/= LT) . compareIndep x . fst . lookup . fst) ps of
              (k, v):_ → map (k:) (go (fst (lookup k)) v)
              _        → case ps of
                           []       → []
                           (k, v):_ → map (k:) (go (fst (lookup k)) v)
          where ps = sortBy (compareIndep `on` fst . lookup . fst) (toKeyedList m)

selectMiddle ∷ Int → [a] → [a]
selectMiddle n xs = take n₁ (reverse b) ++ take n₂ a
  where l = length xs
        (b, a) = splitAt (l `div` 2) xs
        n₁ = n `div` 2
        n₂ = n - n₁

selectUniform ∷ Int → [a] → [a]
selectUniform _ []     = []
selectUniform 0 _      = []
selectUniform 1 (x:_)  = [x]
selectUniform n (hd:tl) = hd : go r tl
  where (d, r) = length tl `divMod` (n - 1)
        go _ [] = []
        go i xs = last b : go (i - 1) a
          where (b, a) = splitAt (if i > 0 then d + 1 else d) xs

selectAzadeh ∷ Int → [a] → [a]
selectAzadeh n xs = take n₁ (reverse a) ++ take n₁ b ++ take n₁ (reverse b) ++ take n₂ c
  where l = length xs
        (a, ys) = splitAt (l `div` 3) xs
        (b, c)  = splitAt (l `div` 3) ys
        n₁ = n `div` 4
        n₂ = n - n₁ * 3
