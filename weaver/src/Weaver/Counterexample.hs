{-# LANGUAGE
    FlexibleContexts,
    MonoLocalBinds,
    UnicodeSyntax
  #-}

module Weaver.Counterexample where

import           Data.Finite.Container (Container, Index)
import           Data.Finite.Small.Map (Map)
import qualified Data.Finite.Small.Map as Map
import           Data.Key (toKeyedList)

data Counterexample c = Nil | Cons (Map (Index c) (Counterexample c))

instance Semigroup (Counterexample c) where
  Nil <> _ = Nil
  _ <> Nil = Nil
  Cons m₁ <> Cons m₂ = Cons (Map.unionWith (<>) m₁ m₂)

instance Monoid (Counterexample c) where
  mempty = Cons Map.empty

instance Eq (Counterexample c) where
  _ == _ = True

singleton ∷ Container c a ⇒ [Index c] → Counterexample c
singleton [] = Nil
singleton (x:xs) = extend x (singleton xs)

getCex ∷ Container c a ⇒ Counterexample c → [[Index c]]
getCex Nil = [[]]
getCex (Cons m) = do
  (a, m') ← toKeyedList m
  x ← getCex m'
  return (a:x)

extend ∷ Container c a ⇒ Index c → Counterexample c → Counterexample c
extend x c = Cons (Map.singleton x c)
