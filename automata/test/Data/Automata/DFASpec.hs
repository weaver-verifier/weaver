{-# LANGUAGE
    BlockArguments,
    PatternSynonyms,
    ScopedTypeVariables,
    UnicodeSyntax
  #-}

module Data.Automata.DFASpec where

import Prelude hiding (null)
import Data.Automata.DFA
import Data.Automata.GraphSpec (G (..))
import Data.Automata.Util (foreach, foreachF, prop)
import Data.Map (Map)
import Data.Maybe (isNothing)
import Data.Proxy (Proxy)
import Test.Hspec (Spec, describe)
import Test.LeanCheck (Listable (..), cons2)

instance Listable (e q) ⇒ Listable (Edge e q) where
  tiers = cons2 Edge

pattern DFA ∷ DFA (Map a) → G (Edge (Map a))
pattern DFA g ← G _ _ g

spec ∷ Spec
spec = do
  describe "isEmpty" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ [a]) (DFA g) →
        not (isEmpty g && member xs g)

  describe "find" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ [a]) (DFA g) →
        case find g of
          Nothing → not (member xs g)
          Just ys → member ys g

  describe "empty" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ [a]) →
        not (member xs (empty ∷ DFA (Map a)))

  describe "null" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ [a]) →
        member xs (null ∷ DFA (Map a)) == (xs == [])

  describe "symbol" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ [a]) x →
        member xs (symbol x ∷ DFA (Map a)) == (xs == [x])

  describe "union" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ [a]) (DFA g₁) (DFA g₂) →
        member xs (union g₁ g₂) == (member xs g₁ || member xs g₂)

  describe "intersection" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ [a]) (DFA g₁) (DFA g₂) →
        member xs (intersection g₁ g₂) == (member xs g₁ && member xs g₂)

  describe "difference" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ [a]) (DFA g₁) (DFA g₂) →
        member xs (difference g₁ g₂) == (member xs g₁ && not (member xs g₂))

  describe "approximate" do
    prop "preserves emptiness" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(DFA (g ∷ DFA (Map a))) →
        isEmpty (approximate g) == isEmpty g

    prop "is subset" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(DFA (g ∷ DFA (Map a))) →
        isSubsetOf (approximate g) g

  describe "isSubsetOf" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(DFA (g₁ ∷ DFA (Map a))) (DFA g₂) →
        isSubsetOf g₁ g₂ == isNothing (findCounterExample g₁ g₂)

  describe "findCounterExample" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ [a]) (DFA g₁) (DFA g₂) →
        case findCounterExample g₁ g₂ of
          Nothing → not (member xs g₁) || member xs g₂
          Just ys → member ys g₁ && not (member ys g₂)
