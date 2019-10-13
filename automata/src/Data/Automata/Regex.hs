{-# LANGUAGE
    DeriveTraversable,
    FlexibleContexts,
    PatternSynonyms,
    ScopedTypeVariables,
    TypeApplications,
    UnicodeSyntax
  #-}

module Data.Automata.Regex (
  Regex (..), member, canonical, derive, toDFA, toNFA
) where

import Prelude hiding (concat, lookup, null, repeat)
import Data.Align (Align (..), Semialign (..))
import Data.Automata.Classes (PointedWithKey (..))
import Data.Automata.DFA (DFA, Edge (..))
import Data.Automata.NFA (NFA, empty, null, symbol, union, concat, shuffle, repeat)
import Data.Automata.Graph (unfold)
import Data.Bifunctor (first)
import Data.Map (Map, lookup)
import Data.Key (Key)
import Data.These (mergeThese)

data Regex a
  = Emp
  | Nil
  | Sym a
  | Alt (Regex a) (Regex a)
  | Cat (Regex a) (Regex a)
  | Par (Regex a) (Regex a)
  | Rep (Regex a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

member ∷ ∀ a. Ord a ⇒ [a] → Regex a → Bool
member []     r = snd (derive @(Map a) r)
member (x:xs) r =
  case lookup x (fst (derive @(Map a) r)) of
    Nothing → False
    Just r' → member xs r'

canonical ∷ Ord a ⇒ Regex a → Regex a
canonical Emp = Emp
canonical Nil = Nil
canonical (Sym x) = Sym x
canonical (Alt r₁ r₂) = alt (canonical r₁) (canonical r₂)
canonical (Cat r₁ r₂) = cat (canonical r₁) (canonical r₂)
canonical (Par r₁ r₂) = par (canonical r₁) (canonical r₂)
canonical (Rep r) = rep (canonical r)

alt ∷ Ord a ⇒ Regex a → Regex a → Regex a
alt Emp x = x
alt x Emp = x
alt (Alt x y) z = alt x (alt y z)
alt x (Alt y z) = case compare x y of
                    LT → Alt x (Alt y z)
                    EQ → Alt y z
                    GT → alt y (alt x z)
alt x y = case compare x y of
            LT → Alt x y
            EQ → x
            GT → alt y x

cat ∷ Ord a ⇒ Regex a → Regex a → Regex a
cat Emp _ = Emp
cat _ Emp = Emp
cat Nil x = x
cat x Nil = x
cat (Cat x y) z = cat x (cat y z)
cat x y = Cat x y

par ∷ Ord a ⇒ Regex a → Regex a → Regex a
par Emp _ = Emp
par _ Emp = Emp
par Nil x = x
par x Nil = x
par (Par x y) z = par x (par y z)
par x (Par y z) = case compare x y of
                    LT → Par x (Par y z)
                    EQ → Par y z
                    GT → par y (par x z)
par x y = case compare x y of
            LT → Par x y
            EQ → x
            GT → par y x

rep ∷ Regex a → Regex a
rep Emp = Nil
rep Nil = Nil
rep (Rep x) = rep x
rep x = Rep x

derive ∷ (Align f, PointedWithKey f, Ord (Key f)) ⇒ Regex (Key f) → (f (Regex (Key f)), Bool)
derive Emp = (nil, False)
derive Nil = (nil, True)
derive (Sym x) = (singleton x Nil, False)
derive (Alt x y) =
  let (δ₁, b₁) = derive x
      (δ₂, b₂) = derive y
  in (alignWith (mergeThese alt) δ₁ δ₂, b₁ || b₂)
derive (Cat x y) =
  let (δ₁, b₁) = first (fmap (`cat` y)) (derive x)
      (δ₂, b₂) = derive y
  in (if b₁ then alignWith (mergeThese alt) δ₁ δ₂ else δ₁, b₁ && b₂)
derive (Par x y) =
  let (δ₁, b₁) = first (fmap (`par` y)) (derive x)
      (δ₂, b₂) = first (fmap ( par  x)) (derive y)
  in (alignWith (mergeThese alt) δ₁ δ₂, b₁ && b₂)
derive (Rep x) =
  let (δ, _) = derive x
  in (fmap (`cat` rep x) δ, True)

toDFA ∷ (Align f, PointedWithKey f, Foldable f, Ord (Key f)) ⇒ Regex (Key f) → DFA f
toDFA = unfold (uncurry Edge . derive)

toNFA ∷ (Align f, PointedWithKey f) ⇒ Regex (Key f) → NFA f
toNFA Emp = empty
toNFA Nil = null
toNFA (Sym x) = symbol x
toNFA (Alt x y) = union (toNFA x) (toNFA y)
toNFA (Cat x y) = concat (toNFA x) (toNFA y)
toNFA (Par x y) = shuffle (toNFA x) (toNFA y)
toNFA (Rep x) = repeat (toNFA x)
