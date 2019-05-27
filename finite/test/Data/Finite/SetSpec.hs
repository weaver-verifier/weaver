{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# LANGUAGE
    BlockArguments,
    PatternSynonyms,
    ScopedTypeVariables,
    TupleSections,
    TypeApplications,
    UnicodeSyntax
  #-}

module Data.Finite.SetSpec where

import           Prelude hiding (map)
import           Data.Finite.Class (Finitary (..), Fun (..))
import qualified Data.Finite.Class as Finite
import           Data.Finite.Set
import           Data.Finite.Util (describeFinite1, foreach, foreachF, prop)
import           Data.List (nub, sort)
import           Data.Proxy (Proxy)
import           Data.These (These (..), these)
import           Test.Hspec (Spec, describe)
import           Test.LeanCheck (Listable (..), (==>), cons1)

instance Finitary a ⇒ Listable (Set a) where
  tiers = cons1 Set

spec ∷ Spec
spec = do
  describeFinite1 @Set "Set"

  describe "isEmpty" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ Set a) →
        isEmpty xs == all (\x → not (member x xs)) Finite.universe

  describe "isSubsetOf" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ Set a) →
      foreach  \(ys ∷ Set a) →
        isSubsetOf xs ys == all (\x → not (member x xs) || member x ys) Finite.universe

    prop "respects ordering" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ Set a) →
      foreach  \(ys ∷ Set a) →
        isSubsetOf xs ys ==> xs <= ys

  describe "empty" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(x ∷ a) →
        not (member x empty)

  describe "universe" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(x ∷ a) →
        member x universe

  describe "singleton" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(x ∷ a) y →
        member x (singleton y) == (x == y)

  describe "insert" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(x ∷ a) y xs →
        member x (insert y xs) == (x == y || member x xs)

  describe "delete" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(x ∷ a) y xs →
        member x (delete y xs) == (x /= y && member x xs)

  describe "union" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(x ∷ a) xs ys →
        member x (union xs ys) == (member x xs || member x ys)

  describe "unions" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \x (xss ∷ [Set a]) →
        member x (unions xss) == any (member x) xss

  describe "intersection" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(x ∷ a) xs ys →
        member x (intersection xs ys) == (member x xs && member x ys)

  describe "intersections" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \x (xss ∷ [Set a]) →
        member x (intersections xss) == all (member x) xss

  describe "difference" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(x ∷ a) xs ys →
        member x (difference xs ys) == (member x xs && not (member x ys))

  describe "complement" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(x ∷ a) xs →
        member x (complement xs) == not (member x xs)

  describe "mapJust" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(x ∷ Maybe a) xs →
        member x (mapJust xs) == maybe False (`member` xs) x
    prop "equals map" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ Set a) →
        mapJust xs == map Just xs

  describe "mapLeft" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreachF \(_ ∷ Proxy b) →
      foreach  \(x ∷ Either a b) xs →
        member x (mapLeft xs) == either (`member` xs) (\_ → False) x
    prop "equals map" $
      foreachF \(_ ∷ Proxy a) →
      foreachF \(_ ∷ Proxy b) →
      foreach  \xs →
        mapLeft xs == (map Left xs ∷ Set (Either a b))

  describe "mapRight" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreachF \(_ ∷ Proxy b) →
      foreach  \(x ∷ Either a b) xs →
        member x (mapRight xs) == either (\_ → False) (`member` xs) x
    prop "equals map" $
      foreachF \(_ ∷ Proxy a) →
      foreachF \(_ ∷ Proxy b) →
      foreach  \xs →
        mapRight xs == (map Right xs ∷ Set (Either a b))

  describe "mapThis" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreachF \(_ ∷ Proxy b) →
      foreach  \(x ∷ These a b) xs →
        member x (mapThis xs) == these (`member` xs) (\_ → False) (\_ _ → False) x
    prop "equals map" $
      foreachF \(_ ∷ Proxy a) →
      foreachF \(_ ∷ Proxy b) →
      foreach  \xs →
        mapThis xs == (map This xs ∷ Set (These a b))

  describe "mapThat" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreachF \(_ ∷ Proxy b) →
      foreach  \(x ∷ These a b) xs →
        member x (mapThat xs) == these (\_ → False) (`member` xs) (\_ _ → False) x
    prop "equals map" $
      foreachF \(_ ∷ Proxy a) →
      foreachF \(_ ∷ Proxy b) →
      foreach  \xs →
        mapThat xs == (map That xs ∷ Set (These a b))

  describe "mapStrongFst" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreachF \(_ ∷ Proxy b) →
      foreach  \(x ∷ a) (xs ∷ Set b) y →
        member y (mapStrongFst x xs) == (fst y == x && member (snd y) xs)
    prop "equals map" $
      foreachF \(_ ∷ Proxy a) →
      foreachF \(_ ∷ Proxy b) →
      foreach \(x ∷ a) (xs ∷ Set b) →
        mapStrongFst x xs == map (x,) xs

  describe "mapStrongSnd" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreachF \(_ ∷ Proxy b) →
      foreach  \(x ∷ a) (xs ∷ Set b) y →
        member y (mapStrongSnd xs x) == (snd y == x && member (fst y) xs)
    prop "equals map" $
      foreachF \(_ ∷ Proxy a) →
      foreachF \(_ ∷ Proxy b) →
      foreach  \(x ∷ a) (xs ∷ Set b) →
        mapStrongSnd xs x == map (,x) xs

  describe "cartesianProduct" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreachF \(_ ∷ Proxy b) →
      foreach  \(x ∷ (a, b)) xs ys →
        member x (cartesianProduct xs ys) ==
          (member (fst x) xs &&
           member (snd x) ys)
    prop "equals map/bind" $
      foreachF \(_ ∷ Proxy a) →
      foreachF \(_ ∷ Proxy b) →
      foreach  \(xs ∷ Set a) (ys ∷ Set b) →
        cartesianProduct xs ys == bind (\x → map (x,) ys) xs

  describe "toList" do
    prop "contains all elements" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(x ∷ a) xs →
        member x xs == (x `elem` toList xs)
    prop "contains no duplicates" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ Set a) →
        toList xs == nub (toList xs)
    prop "is sorted" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ Set a) →
        toList xs == sort (toList xs)

  describe "fromList" do
    prop "contains all elements" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(x ∷ a) xs →
        member x (fromList xs) == (x `elem` xs)

  describe "map" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreachF \(_ ∷ Proxy b) →
      foreach  \(Fun (f ∷ a → b)) y xs →
        member y (map f xs) == any (\x → f x == y) (toList xs)
    prop "respects identity" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ Set a) →
        map id xs == xs
    prop "respects compositition" $
      foreachF \(_ ∷ Proxy a) →
      foreachF \(_ ∷ Proxy b) →
      foreachF \(_ ∷ Proxy c) →
      foreach  \(Fun f ∷ Fun b c) (Fun g ∷ Fun a b) xs →
        map (f . g) xs == map f (map g xs)
    prop "equals bind" $
      foreachF \(_ ∷ Proxy a) →
      foreachF \(_ ∷ Proxy b) →
      foreach  \(Fun (f ∷ a → b)) xs →
        map f xs == bind (singleton . f) xs

  describe "bind" do
    prop "is correct" $
      foreachF \(_ ∷ Proxy a) →
      foreachF \(_ ∷ Proxy b) →
      foreach  \(Fun (f ∷ a → Set b)) y xs →
        member y (bind f xs) == any (\x → member y (f x)) (toList xs)
    prop "respects identity" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ Set a) →
        bind singleton xs == xs
    prop "respects compositition" $
      foreachF \(_ ∷ Proxy a) →
      foreachF \(_ ∷ Proxy b) →
      foreachF \(_ ∷ Proxy c) →
      foreach  \(Fun f ∷ Fun b (Set c)) (Fun g ∷ Fun a (Set b)) xs →
        bind (bind f . g) xs == bind f (bind g xs)
