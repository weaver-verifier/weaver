{-# LANGUAGE
    BlockArguments,
    PatternSynonyms,
    ScopedTypeVariables,
    TupleSections,
    TypeApplications,
    UnicodeSyntax
  #-}

module Data.Finite.Set.AntichainSpec where

import           Data.Finite.Class (Finitary (..))
import qualified Data.Finite.Class as Finite
import           Data.Finite.Set (Set, isSubsetOf)
import qualified Data.Finite.Set as Set
import           Data.Finite.Set.Antichain
import           Data.Finite.SetSpec ()
import           Data.Finite.Util (foreachF, foreach, prop)
import           Data.Proxy (Proxy)
import           Test.Hspec (Spec, describe)
import           Test.LeanCheck (Listable (..), cons1)

instance (Finitary a, Listable a) ⇒ Listable (Antichain a) where
  tiers = cons1 fromList

isAscending ∷ Ord a ⇒ [a] → Bool
isAscending [] = True
isAscending [_] = True
isAscending (x:y:xs) = x < y && isAscending (y:xs)

spec ∷ Spec
spec = do
  describe "(==)" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xss ∷ Antichain a) yss →
        (xss == yss) == all (\xs → member xs xss == member xs yss) Finite.universe

  describe "isEmpty" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xss ∷ Antichain a) xs →
        not (isEmpty xss && member xs xss)

  describe "toList" do
    prop "has non-comparable elements" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xss ∷ Antichain a) →
        and do xs ← toList xss
               ys ← toList xss
               pure (not (isSubsetOf xs ys || isSubsetOf ys xs) || xs == ys)

    prop "is included in antichain" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xss ∷ Antichain a) →
        all (`member` xss) (toList xss)

    prop "contains a superset of every member" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ Set a) xss →
        member xs xss == any (isSubsetOf xs) (toList xss)

  describe "fromList" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ Set a) xss →
        member xs (fromList xss) == any (isSubsetOf xs) xss

  describe "empty" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ Set a) →
        not (member xs empty)

  describe "universe" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ Set a) →
        member xs universe

  describe "singleton" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ Set a) ys →
        member xs (singleton ys) == isSubsetOf xs ys

  describe "insert" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ Set a) ys zss →
        member xs (insert ys zss) == (isSubsetOf xs ys || member xs zss)

    prop "is ascending" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ Set a) yss →
        isAscending (toList (insert xs yss))

  describe "tryInsert" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ Set a) yss →
        case tryInsert xs yss of
          Nothing  → member xs yss
          Just zss → insert xs yss == zss

    prop "is ascending" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ Set a) yss →
        case tryInsert xs yss of
          Nothing → True
          Just zss → isAscending (toList zss)

  describe "union" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ Set a) yss zss →
        member xs (union yss zss) == (member xs yss || member xs zss)

    prop "is ascending" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xss ∷ Antichain a) yss →
        isAscending (toList (union xss yss))

    prop "is equivalent to naive implementation" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xss ∷ Antichain a) yss →
        union xss yss == foldr insert xss (toList yss)

  describe "unions" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \xs (xsss ∷ [Antichain a]) →
        member xs (unions xsss) == any (member xs) xsss

    prop "is ascending" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xss ∷ [Antichain a]) →
        isAscending (toList (unions xss))

  describe "reduce" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ Set a) ys zss →
        member xs (reduce ys zss) ==
          any (isSubsetOf xs . Set.intersection ys) (toList zss)

    prop "is ascending" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ Set a) yss →
        isAscending (toList (reduce xs yss))

  describe "intersection" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ Set a) yss zss →
        member xs (intersection yss zss) == (member xs yss && member xs zss)

    prop "is ascending" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xss ∷ Antichain a) yss →
        isAscending (toList (intersection xss yss))

  describe "intersections" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \xs (xsss ∷ [Antichain a]) →
        member xs (intersections xsss) == all (member xs) xsss

    prop "is ascending" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xss ∷ [Antichain a]) →
        isAscending (toList (intersections xss))
