{-# LANGUAGE
    BlockArguments,
    ScopedTypeVariables,
    TemplateHaskell,
    UnicodeSyntax
  #-}

module Data.Automata.RegexSpec where

import           Data.Automata.Regex
import           Data.Automata.DFA (DFA)
import qualified Data.Automata.DFA as DFA
import           Data.Automata.NFA (NFA)
import qualified Data.Automata.NFA as NFA
import           Data.Automata.Util (foreachF, foreach, splits, separations, parts, prop)
import           Data.Proxy (Proxy (..))
import           Data.Map (Map)
import           Test.Hspec (Spec, describe)
import           Test.LeanCheck (Listable (..), (\/), cons0, cons1, cons2)

instance Listable a ⇒ Listable (Regex a) where
  tiers = cons0 Emp \/ cons0 Nil \/ cons1 Sym
       \/ cons2 Alt \/ cons2 Cat \/ cons2 Par

spec ∷ Spec
spec = do
  describe "member" do
    prop "is correct (Emp)" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ [a]) →
        not (member xs Emp)
    prop "is correct (Nil)" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ [a]) →
        member xs Nil == null xs
    prop "is correct (Sym)" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ [a]) x →
        member xs (Sym x) == (xs == [x])
    prop "is correct (Alt)" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ [a]) r₁ r₂ →
        member xs (Alt r₁ r₂) == (member xs r₁ || member xs r₂)
    prop "is correct (Cat)" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ [a]) r₁ r₂ →
        member xs (Cat r₁ r₂) ==
        any (\(l, r) → member l r₁ && member r r₂) (splits xs)
    prop "is correct (Par)" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ [a]) r₁ r₂ →
        member xs (Par r₁ r₂) ==
        any (\(l, r) → member l r₁ && member r r₂) (separations xs)
    prop "is correct (Rep)" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ [a]) r →
        member xs (Rep r) == any (all (`member` r)) (parts xs)

  describe "canonical" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ [a]) r →
        member xs (canonical r) == member xs r

  describe "toDFA" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ [a]) r →
        DFA.member xs (toDFA r ∷ DFA (Map a)) == member xs r

  describe "toNFA" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ [a]) r →
        NFA.member xs (toNFA r ∷ NFA (Map a)) == member xs r
