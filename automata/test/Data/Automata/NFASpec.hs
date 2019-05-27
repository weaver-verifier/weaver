{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# LANGUAGE
    BlockArguments,
    PatternSynonyms,
    ScopedTypeVariables,
    UndecidableInstances,
    UnicodeSyntax
  #-}

module Data.Automata.NFASpec where

import           Prelude hiding (concat, null, repeat)
import           Data.Automata.GraphSpec (G (..))
import           Data.Automata.DFA (DFA)
import qualified Data.Automata.DFA as DFA
import           Data.Automata.DFASpec (pattern DFA)
import           Data.Automata.NFA
import           Data.Automata.Util (foreach, foreachF, splits, parts, separations, prop)
import           Data.Finite.Set (Set)
import           Data.Map (Map)
import           Data.Maybe (isNothing)
import           Data.Proxy (Proxy)
import           Test.Hspec (Spec, describe)
import           Test.LeanCheck (Listable (..), cons2)

instance Listable (e (Set q)) ⇒ Listable (Edge e q) where
  tiers = cons2 Edge

pattern NFA ∷ NFA (Map a) → G (Edge (Map a))
pattern NFA g ← G _ _ g

spec ∷ Spec
spec = do
  describe "empty" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ [a]) →
        not (member xs (empty ∷ NFA (Map a)))

  describe "null" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ [a]) →
        member xs (null ∷ NFA (Map a)) == (xs == [])

  describe "symbol" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ [a]) x →
        member xs (symbol x ∷ NFA (Map a)) == (xs == [x])

  describe "union" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ [a]) (NFA g₁) (NFA g₂) →
        member xs (union g₁ g₂) == (member xs g₁ || member xs g₂)

  describe "intersection" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ [a]) (NFA g₁) (NFA g₂) →
        member xs (intersection g₁ g₂) == (member xs g₁ && member xs g₂)

  describe "difference" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ [a]) (NFA g₁) (DFA g₂) →
        member xs (difference g₁ g₂) == (member xs g₁ && not (DFA.member xs g₂))

  describe "concat" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ [a]) (NFA g₁) (NFA g₂) →
        member xs (concat g₁ g₂) ==
          any (\(l, r) → member l g₁ && member r g₂) (splits xs)

  describe "repeat" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ [a]) (NFA g) →
        member xs (repeat g) == any (all (`member` g)) (parts xs)

  describe "shuffle" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ [a]) (NFA g₁) (NFA g₂) →
        member xs (shuffle g₁ g₂) ==
        any (\(l, r) → member l g₁ && member r g₂) (separations xs)

  describe "fromDFA" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ [a]) (DFA g) →
        member xs (fromDFA g) == DFA.member xs g

  describe "toDFA" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ [a]) (NFA g) →
        DFA.member xs (toDFA g) == member xs g

  describe "isSubsetOf" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(NFA (g₁ ∷ NFA (Map a))) (NFA g₂) →
        isSubsetOf g₁ g₂ == isNothing (findCounterExample g₁ g₂)

    prop "is equivalent to the DFA version" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(DFA (g₁ ∷ DFA (Map a))) (DFA g₂) →
        DFA.isSubsetOf g₁ g₂ == isSubsetOf (fromDFA g₁) (fromDFA g₂)

  describe "findCounterExample" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ [a]) (NFA g₁) (NFA g₂) →
        case findCounterExample g₁ g₂ of
          Nothing → not (member xs g₁) || member xs g₂
          Just ys → member ys g₁ && not (member ys g₂)

    prop "is equivalent to the DFA version" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(DFA (g₁ ∷ DFA (Map a))) (DFA g₂) →
        isNothing (DFA.findCounterExample g₁ g₂) ==
          isNothing (findCounterExample (fromDFA g₁) (fromDFA g₂))
