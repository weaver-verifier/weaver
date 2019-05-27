{-# LANGUAGE
    ApplicativeDo,
    BlockArguments,
    StandaloneDeriving,
    UndecidableInstances,
    UnicodeSyntax
  #-}

module Data.Automata.NFA (
  Edge (..), NFAM, NFA,
  member, memberM,
  empty, null, symbol,
  union, intersection, difference,
  concat, repeat, shuffle,
  fromDFA, toDFA,
  isSubsetOf, isSubsetOfM,
  findCounterExample, findCounterExampleM
) where

import           Prelude hiding (concat, lookup, null, repeat)
import           Data.Align (Align (..), salign)
import           Data.Automata.Classes (PointedWithKey (..), Absorb (..))
import           Data.Automata.Graph (GraphM (..), Graph)
import           Data.Automata.DFA (DFAM)
import qualified Data.Automata.DFA as DFA
import           Data.Functor.Apply (Apply (..), liftF2)
import           Data.Functor.Identity (Identity (..))
import           Data.Finite.Set (Set)
import qualified Data.Finite.Set as Set
import qualified Data.Finite.Set.Antichain as AC
import           Data.Key (Key, Lookup (..), FoldableWithKey (..))
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe, isNothing, mapMaybe)

data Edge f a = Edge {
  delta ∷ f (Set a),
  final ∷ Bool
}

deriving instance Show (f (Set a)) ⇒ Show (Edge f a)

type NFAM m f = GraphM m (Edge f)
type NFA    f = Graph    (Edge f)

member ∷ Lookup f ⇒ [Key f] → NFA f → Bool
member xs = runIdentity . memberM xs

memberM ∷ (Monad m, Lookup f) ⇒ [Key f] → NFAM m f → m Bool
memberM word (UnfoldM next root) = go (Set.singleton root) word
  where go qs xs' = do
          edges ← traverse next (Set.toList qs)
          case xs' of
            []   → return (any final edges)
            x:xs → go (Set.unions (mapMaybe (lookup x . delta) edges)) xs

setmap ∷ Functor f ⇒ (Set a → Set b) → Edge f a → Edge f b
setmap f (Edge δ b) = Edge (fmap f δ) b

empty ∷ (Applicative m, Align f) ⇒ NFAM m f
empty = UnfoldM (\_ → pure (Edge nil False)) ()

null ∷ (Applicative m, Align f) ⇒ NFAM m f
null = UnfoldM (\_ → pure (Edge nil True)) ()

symbol ∷ (Applicative m, Align f, PointedWithKey f) ⇒ Key f → NFAM m f
symbol x = UnfoldM (pure . next) False
  where next False = Edge (singleton x (Set.singleton True)) False
        next True  = Edge nil True

union ∷ (Applicative m, Align f) ⇒ NFAM m f → NFAM m f → NFAM m f
union (UnfoldM next₁ root₁) (UnfoldM next₂ root₂) = UnfoldM next root
  where root = Nothing
        next (Just (Left  q₁)) = next₁' q₁
        next (Just (Right q₂)) = next₂' q₂
        next Nothing = do
          ~(Edge δ₁ b₁) ← next₁' root₁
          ~(Edge δ₂ b₂) ← next₂' root₂
          pure (Edge (salign δ₁ δ₂) (b₁ || b₂))

        next₁' = fmap (setmap (Set.mapJust . Set.mapLeft))  . next₁
        next₂' = fmap (setmap (Set.mapJust . Set.mapRight)) . next₂

intersection ∷ (Applicative m, Apply f) ⇒ NFAM m f → NFAM m f → NFAM m f
intersection (UnfoldM next₁ root₁) (UnfoldM next₂ root₂) = UnfoldM next root
  where root = (root₁, root₂)
        next (q₁, q₂) = do
          ~(Edge δ₁ b₁) ← next₁ q₁
          ~(Edge δ₂ b₂) ← next₂ q₂
          pure (Edge (liftF2 Set.cartesianProduct δ₁ δ₂) (b₁ && b₂))

difference ∷ (Applicative m, Absorb f) ⇒ NFAM m f → DFAM m f → NFAM m f
difference (UnfoldM next₁ root₁) (UnfoldM next₂ root₂) = UnfoldM next root
  where root = (Just root₂, root₁)
        next (Nothing, q₁) = fmap (setmap (Set.mapStrongFst Nothing)) (next₁ q₁)
        next (Just q₂, q₁) = do
          ~(    Edge δ₁ b₁) ← next₁ q₁
          ~(DFA.Edge δ₂ b₂) ← next₂ q₂
          pure (Edge (absorbWith (flip Set.mapStrongFst) δ₁ δ₂) (b₁ && not b₂))

concat ∷ (Monad m, Align f) ⇒ NFAM m f → NFAM m f → NFAM m f
concat (UnfoldM next₁ root₁) (UnfoldM next₂ root₂) = UnfoldM next root
  where root = Left root₁
        next (Left q₁) = do
          ~e@(Edge δ₁ b₁) ← next₁' q₁
          if b₁ then do
            ~(Edge δ₂ b₂) ← next₂' root₂
            pure (Edge (salign δ₁ δ₂) b₂)
          else
            pure e
        next (Right q₂) = next₂' q₂

        next₁' = fmap (setmap Set.mapLeft)  . next₁
        next₂' = fmap (setmap Set.mapRight) . next₂

repeat ∷ (Monad m, Align f) ⇒ NFAM m f → NFAM m f
repeat (UnfoldM next root) = UnfoldM next' root'
  where root' = Nothing
        next' Nothing = do
          ~(Edge δ _) ← next'' root
          pure (Edge δ True)
        next' (Just q) = do
          ~e@(Edge δ b) ← next'' q
          if b then do
            ~(Edge δ' _) ← next'' root
            pure (Edge (salign δ δ') True)
          else
            pure e

        next'' = fmap (setmap Set.mapJust) . next

shuffle ∷ (Applicative m, Align f) ⇒ NFAM m f → NFAM m f → NFAM m f
shuffle (UnfoldM next₁ root₁) (UnfoldM next₂ root₂) = UnfoldM next root
  where root = (root₁, root₂)
        next (q₁, q₂) = do
          ~(Edge δ₁ b₁) ← setmap (`Set.mapStrongSnd` q₂) <$> next₁ q₁
          ~(Edge δ₂ b₂) ← setmap ( Set.mapStrongFst  q₁) <$> next₂ q₂
          pure (Edge (salign δ₁ δ₂) (b₁ && b₂))

fromDFA ∷ (Functor m, Functor f) ⇒ DFAM m f → NFAM m f
fromDFA (UnfoldM next root) = UnfoldM next' root
  where next' q = do
          ~(DFA.Edge δ b) ← next q
          pure (Edge (fmap Set.singleton δ) b)

toDFA ∷ (Monad m, Align f) ⇒ NFAM m f → DFAM m f
toDFA (UnfoldM next root) = UnfoldM
  (\qs → do es ← traverse next (Set.toList qs)
            let δ = foldr (salign . delta) nil es
                b = any final es
            pure (DFA.Edge δ b))
  (Set.singleton root)

isSubsetOf ∷ (Absorb f, FoldableWithKey f) ⇒ NFA f → NFA f → Bool
isSubsetOf nfa₁ nfa₂ = runIdentity (isSubsetOfM nfa₁ nfa₂)

isSubsetOfM ∷ (Monad m, Absorb f, FoldableWithKey f) ⇒ NFAM m f → NFAM m f → m Bool
isSubsetOfM nfa₁ nfa₂ = isNothing <$> findCounterExampleM nfa₁ nfa₂

findCounterExample ∷ (Absorb f, FoldableWithKey f) ⇒ NFA f → NFA f → Maybe [Key f]
findCounterExample nfa₁ nfa₂ = runIdentity (findCounterExampleM nfa₁ nfa₂)

findCounterExampleM ∷ (Monad m, Absorb f, FoldableWithKey f) ⇒ NFAM m f → NFAM m f → m (Maybe [Key f])
findCounterExampleM (UnfoldM next₁ root₁) (UnfoldM next₂ root₂) =
    explore Map.empty (newQueue (root₁, Set.singleton root₂, []))
  where explore cache queue =
          case dequeue queue of
            Nothing → return Nothing
            Just ((q₁, q₂, ks), queue') → do
              ~(Edge δ₁ b₁) ← next₁ q₁
              es ← traverse next₂ (Set.toList q₂)
              let δ₂ = foldr (salign . delta) nil es
                  b₂ = any final es
              if b₁ && not b₂ then
                return (Just (reverse ks))
              else do
                let ac = Map.findWithDefault AC.empty q₁ cache
                case AC.tryInsert (Set.complement q₂) ac of
                  Nothing → explore cache queue'
                  Just ac' → do
                    let succs = do
                          (k, (q₁'s, q₂')) ← toKeyedList (absorb δ₁ δ₂)
                          q₁' ← Set.toList q₁'s
                          return (q₁', fromMaybe Set.empty q₂', k:ks)
                    explore (Map.insert q₁ ac' cache) (enqueue succs queue')

type Queue a = ([a], [a])

newQueue ∷ a → Queue a
newQueue x = ([x], [])

dequeue ∷ Queue a → Maybe (a, Queue a)
dequeue (x:xs, ys) = Just (x, (xs, ys))
dequeue ([], [])   = Nothing
dequeue ([], ys)   = dequeue (reverse ys, [])

enqueue ∷ [a] → Queue a → Queue a
enqueue zs (xs, ys) = (xs, zs ++ ys)
