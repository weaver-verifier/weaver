{-# LANGUAGE
    FlexibleContexts,
    ImplicitParams,
    MonoLocalBinds,
    UnicodeSyntax
  #-}

module Weaver.Counterexample where

import           Prelude hiding (lookup, not)
import           Data.Bifunctor (bimap)
import           Data.Finite.Container (Container, Index, lookup)
import           Data.Finite.Set (Set, toList)
import           Data.Finite.Small.Map (Map)
import qualified Data.Finite.Small.Map as Map
import           Data.Key (toKeyedList)
import           Language.SMT.Expr (not)
import           Weaver.Config
import           Weaver.Program (Tag)
import           Weaver.Stmt (Stmt, artificial, indep)

data Counterexample c
  = Nil
  | Cons (Set (Index c, Index c)) (Map (Index c) (Counterexample c))

instance Semigroup (Counterexample c) where
  Nil <> _ = Nil
  _ <> Nil = Nil
  Cons c₁ m₁ <> Cons c₂ m₂ = Cons (c₁ <> c₂) (Map.unionWith (<>) m₁ m₂)

instance Monoid (Counterexample c) where
  mempty = Cons mempty Map.empty

instance Eq (Counterexample c) where
  _ == _ = True

singleton ∷ Container c a ⇒ [Index c] → Counterexample c
singleton [] = Nil
singleton (x:xs) = extend x (singleton xs)

getCex ∷ (Container c ([Tag], Stmt), ?config ∷ Config) ⇒ Counterexample c → [[Stmt]]
getCex Nil = [[]]
getCex (Cons c m) = indeps c ++ do
    (a, m') ← toKeyedList m
    x ← getCex m'
    return (snd (lookup a) : x)

extend ∷ Container c a ⇒ Index c → Counterexample c → Counterexample c
extend x c = Cons mempty (Map.singleton x c)

extend' ∷ Container c a ⇒ Set (Index c, Index c) → Index c → Counterexample c → Counterexample c
extend' x y c = Cons x (Map.singleton y c)

indeps ∷ (Container c ([Tag], Stmt), ?config ∷ Config) ⇒ Set (Index c, Index c) → [[Stmt]]
indeps = map (:[])
       . map artificial
       . map not
       . map (uncurry indep)
       . map (bimap (snd . lookup) (snd . lookup))
       . toList
