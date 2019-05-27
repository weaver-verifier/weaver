{-# LANGUAGE
    ApplicativeDo,
    DeriveTraversable,
    FlexibleContexts,
    TupleSections,
    UnicodeSyntax
  #-}

module Data.Automata.DFA (
  Edge (..), DFAM, DFA,
  member, memberM, isEmpty, find,
  empty, null, symbol,
  union, intersection,
  difference, approximate,
  isSubsetOf, findCounterExample
) where

import Prelude hiding (lookup, null)
import Control.Applicative ((<|>))
import Data.Align (Align (..))
import Data.Automata.Classes (PointedWithKey (..), Absorb (..))
import Data.Automata.Graph (GraphM (..), Graph, foldCut)
import Data.Functor.Apply (Apply (..), liftF2)
import Data.Functor.Identity (Identity (..))
import Data.Key (Key, Lookup (..), FoldableWithKey (..))
import Data.Maybe (isJust)
import Data.These (These (..))

data Edge f a = Edge {
  delta ∷ f a,
  final ∷ Bool
} deriving (Foldable, Functor, Show, Traversable)

type DFAM m f = GraphM m (Edge f)
type DFA    f = Graph    (Edge f)

member ∷ Lookup f ⇒ [Key f] → DFA f → Bool
member xs = runIdentity . memberM xs

memberM ∷ (Monad m, Lookup f) ⇒ [Key f] → DFAM m f → m Bool
memberM []     (UnfoldM next root) = final <$> next root
memberM (x:xs) (UnfoldM next root) = do
  ~(Edge δ _) ← next root
  case lookup x δ of
    Nothing    → pure False
    Just root' → memberM xs (UnfoldM next root')

isEmpty ∷ Foldable f ⇒ DFA f → Bool
isEmpty = foldCut (\k (Edge δ b) → not b && all k δ) True not

find ∷ (FoldableWithKey f, Eq (Key f)) ⇒ DFA f → Maybe [Key f]
find = getFind . foldCut go mempty (isJust . getFind)
  where go _ (Edge _ True)  = Find (Just [])
        go k (Edge δ False) = foldMapWithKey (\x q → fmap (x:) (k q)) δ

newtype Find a = Find { getFind ∷ Maybe a }
  deriving Functor

instance Eq (Find a) where
  Find x == Find y = isJust x == isJust y

instance Semigroup (Find a) where
  Find x <> Find y = Find (x <|> y)

instance Monoid (Find a) where
  mempty = Find Nothing

empty ∷ (Applicative m, Align f) ⇒ DFAM m f
empty = UnfoldM (\_ → pure (Edge nil False)) ()

null ∷ (Applicative m, Align f) ⇒ DFAM m f
null = UnfoldM (\_ → pure (Edge nil True)) ()

symbol ∷ (Applicative m, Align f, PointedWithKey f) ⇒ Key f → DFAM m f
symbol x = UnfoldM (pure . next) False
  where next False = Edge (singleton x True) False
        next True  = Edge nil True

union ∷ (Applicative m, Align f) ⇒ DFAM m f → DFAM m f → DFAM m f
union (UnfoldM next₁ root₁) (UnfoldM next₂ root₂) = UnfoldM next root
  where root = These root₁ root₂
        next (This q₁) = fmap (fmap This) (next₁ q₁)
        next (That q₂) = fmap (fmap That) (next₂ q₂)
        next (These q₁ q₂) = do
          ~(Edge δ₁ b₁) ← next₁ q₁
          ~(Edge δ₂ b₂) ← next₂ q₂
          pure (Edge (align δ₁ δ₂) (b₁ || b₂))

intersection ∷ (Applicative m, Apply f) ⇒ DFAM m f → DFAM m f → DFAM m f
intersection (UnfoldM next₁ root₁) (UnfoldM next₂ root₂) = UnfoldM next root
  where root = (root₁, root₂)
        next (q₁, q₂) = do
          ~(Edge δ₁ b₁) ← next₁ q₁
          ~(Edge δ₂ b₂) ← next₂ q₂
          pure (Edge (liftF2 (,) δ₁ δ₂) (b₁ && b₂))

difference ∷ (Applicative m, Absorb f) ⇒ DFAM m f → DFAM m f → DFAM m f
difference (UnfoldM next₁ root₁) (UnfoldM next₂ root₂) = UnfoldM next root
  where root = (root₁, Just root₂)
        next (q₁, Nothing) = fmap (fmap (, Nothing)) (next₁ q₁)
        next (q₁, Just q₂) = do
          ~(Edge δ₁ b₁) ← next₁ q₁
          ~(Edge δ₂ b₂) ← next₂ q₂
          pure (Edge (absorb δ₁ δ₂) (b₁ && not b₂))

approximate ∷ (Functor m, Absorb f) ⇒ DFAM m f → DFAM m f
approximate (UnfoldM next root) = UnfoldM next' root'
  where root' = root
        next' = fmap (\(Edge δ b) → Edge (if b then nil else δ) b) . next

isSubsetOf ∷ (Absorb f, Foldable f) ⇒ DFA f → DFA f → Bool
isSubsetOf dfa₁ dfa₂ = isEmpty (approximate (difference dfa₁ dfa₂))

findCounterExample ∷ (Absorb f, FoldableWithKey f, Eq (Key f)) ⇒ DFA f → DFA f → Maybe [Key f]
findCounterExample dfa₁ dfa₂ = find (approximate (difference dfa₁ dfa₂))
