{-# LANGUAGE
    BlockArguments,
    PatternSynonyms,
    ScopedTypeVariables,
    TupleSections,
    TypeApplications,
    UnicodeSyntax
  #-}

module Data.Finite.Set.AntiMapSpec where

import           Prelude hiding (lookup)
import           Data.Finite.Class (Finitary (..))
import qualified Data.Finite.Class as Finite
import           Data.Finite.Set (Set, isSubsetOf)
import           Data.Finite.Set.AntiMap
import           Data.Finite.SetSpec ()
import           Data.Finite.Util (foreachF, foreach, prop)
import           Data.Proxy (Proxy)
import           Test.Hspec (Spec, describe)
import           Test.LeanCheck (Listable (..), cons1)

instance (Finitary k, Listable k, Listable a) ⇒ Listable (AntiMap k a) where
  tiers = cons1 fromList

isAscending ∷ Ord k ⇒ [(k, a)] → Bool
isAscending [] = True
isAscending [_] = True
isAscending (x:y:xs) = fst x < fst y && isAscending (y:xs)

spec ∷ Spec
spec = do
  describe "(==)" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy k) →
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xss ∷ AntiMap k a) yss →
        (xss == yss) == all (\xs → lookup xs xss == lookup xs yss) Finite.universe

  describe "isEmpty" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy k) →
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xss ∷ AntiMap k a) xs →
        not (isEmpty xss && member xs xss)

  describe "toList" do
    prop "has non-comparable elements" $
      foreachF \(_ ∷ Proxy k) →
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xss ∷ AntiMap k a) →
        and do (xs, _) ← toList xss
               (ys, _) ← toList xss
               pure (not (isSubsetOf xs ys || isSubsetOf ys xs) || xs == ys)

    prop "is included in AntiMap k" $
      foreachF \(_ ∷ Proxy k) →
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xss ∷ AntiMap k a) →
        all (\(k, v) → lookup k xss == Just v) (toList xss)

    prop "contains a superset of every member" $
      foreachF \(_ ∷ Proxy k) →
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ Set k) (xss ∷ AntiMap k a) →
        member xs xss == any (isSubsetOf xs . fst) (toList xss)

  describe "fromList" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy k) →
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ Set k) (xss ∷ [(Set k, a)]) →
        member xs (fromList xss) == any (isSubsetOf xs . fst) xss

  describe "empty" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy k) →
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ Set k) →
        not (member xs empty)

  describe "universe" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy k) →
      foreachF \(_ ∷ Proxy a) →
      foreach  \(x ∷ a) (xs ∷ Set k) →
        member xs (universe x)

  describe "singleton" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy k) →
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ Set k) ys (x ∷ a) →
        member xs (singleton ys x) == isSubsetOf xs ys

  describe "insert" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy k) →
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ Set k) ys (x ∷ a) zss →
        member xs (insert ys x zss) == (isSubsetOf xs ys || member xs zss)

    prop "is ascending" $
      foreachF \(_ ∷ Proxy k) →
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ Set k) (x ∷ a) yss →
        isAscending (toList (insert xs x yss))

  describe "union" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy k) →
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ Set k) (yss ∷ AntiMap k a) zss →
        member xs (union yss zss) == (member xs yss || member xs zss)

    prop "is ascending" $
      foreachF \(_ ∷ Proxy k) →
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xss ∷ AntiMap k a) yss →
        isAscending (toList (union xss yss))

    prop "is equivalent to naive implementation" $
      foreachF \(_ ∷ Proxy k) →
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xss ∷ AntiMap k a) yss →
        union xss yss == foldr (uncurry (insertWith (flip const))) xss (toList yss)

  describe "unions" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy k) →
      foreachF \(_ ∷ Proxy a) →
      foreach  \xs (xsss ∷ [AntiMap k a]) →
        member xs (unions xsss) == any (member xs) xsss

    prop "is ascending" $
      foreachF \(_ ∷ Proxy k) →
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xss ∷ [AntiMap k a]) →
        isAscending (toList (unions xss))

  describe "intersection" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy k) →
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ Set k) (yss ∷ AntiMap k a) zss →
        member xs (intersection yss zss) == (member xs yss && member xs zss)

    prop "is ascending" $
      foreachF \(_ ∷ Proxy k) →
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xss ∷ AntiMap k a) yss →
        isAscending (toList (intersection xss yss))

  describe "intersections" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy k) →
      foreachF \(_ ∷ Proxy a) →
      foreach  \x xs (xsss ∷ [AntiMap k a]) →
        member xs (intersections x xsss) == all (member xs) xsss

    prop "is ascending" $
      foreachF \(_ ∷ Proxy k) →
      foreachF \(_ ∷ Proxy a) →
      foreach  \x (xss ∷ [AntiMap k a]) →
        isAscending (toList (intersections x xss))
