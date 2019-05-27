{-# LANGUAGE
    AllowAmbiguousTypes,
    BlockArguments,
    QuantifiedConstraints,
    RankNTypes,
    ScopedTypeVariables,
    TypeApplications,
    UnicodeSyntax
  #-}

module Data.Finite.Util where

import Data.Finite (Finite, finites)
import Data.Finite.Class
import Data.Proxy (Proxy (..))
import Data.These (These (..))
import Data.Void (Void)
import GHC.TypeLits (KnownNat, SomeNat (..), someNatVal)
import Test.Hspec (Spec, describe, it)
import Test.Hspec.LeanCheck (propertyFor)
import Test.LeanCheck (Listable (..), (\/), cons0, cons1, cons2)
import Test.LeanCheck.Core (Testable (..))
import Test.LeanCheck.Function ()
import Test.LeanCheck.Utils.Types (Natural (..))

instance Listable Void where
  tiers = []

instance Listable (Proxy k) where
  tiers = cons0 Proxy

instance (Listable a, Listable b) ⇒ Listable (These a b) where
  tiers = cons1 This \/ cons1 That \/ cons2 These

instance (Listable a, Eq a, Listable b) ⇒ Listable (Fun a b) where
  tiers = cons1 Fun

instance KnownNat n ⇒ Listable (Finite n) where
  list = finites

newtype Prop = Prop [[([String], Bool)]]

instance Testable Prop where
  resultiers (Prop xs) = xs

foreach ∷ (Listable a, Show a, Testable b) ⇒ (a → b) → Prop
foreach = Prop . resultiers

foreachF ∷ Testable a ⇒ (∀ b. (Finitary b, Listable b, Ord b, Show b) ⇒ Proxy b → a) → Prop
foreachF f = foreachN \(_ ∷ Proxy n) → f (Proxy @(Finite n))

foreachN ∷ Testable a ⇒ (∀ n. KnownNat n ⇒ Proxy n → a) → Prop
foreachN f = foreach \(Natural x) →
  case someNatVal x of
    Just (SomeNat y) → f y
    Nothing → error "foreachN: impossible"

newtype Index a = Index (Finite (Size a))

instance Show (Index a) where
  show (Index x) = show x

instance Finitary a ⇒ Listable (Index a) where
  tiers = cons1 Index

prop ∷ Testable a ⇒ String → a → Spec
prop xs p = it xs (propertyFor 10000 p)

describeFinite ∷ ∀ a. (Finitary a, Listable a, Show a) ⇒ String → Spec
describeFinite name = describe ("Finitary " ++ name) do
  prop "is bijection (1)" \(x ∷ a) →
    decode (encode x) == x
  prop "is bijection (2)" \(x ∷ Finite (Size a)) →
    encode (decode x ∷ a) == x
  prop "respects comparison" \(x ∷ a) y →
    compare x y == compare (encode x) (encode y)

describeFinite1 ∷ ∀ f. (∀ a. (Finitary a, Listable a, Ord a, Show a) ⇒ (Finitary (f a), Listable (f a), Show (f a))) ⇒ String → Spec
describeFinite1 name = describe ("Finitary " ++ name) do
  prop "is bijection (1)" $
    foreachF \(_ ∷ Proxy a) →
    foreach  \(x ∷ f a) →
      decode (encode x) == x
  prop "is bijection (2)" $
    foreachF \(_ ∷ Proxy a) →
    foreach  \(Index x ∷ Index (f a)) →
      encode (decode x ∷ f a) == x
  prop "respects comparison" $
    foreachF \(_ ∷ Proxy a) →
    foreach  \(x ∷ f a) →
    foreach  \(y ∷ f a) →
      compare x y == compare (encode x) (encode y)

describeFinite2 ∷ ∀ f. (∀ a b. (Finitary a, Listable a, Ord a, Show a, Finitary b, Listable b, Ord b, Show b) ⇒ (Finitary (f a b), Listable (f a b), Show (f a b))) ⇒ String → Spec
describeFinite2 name = describe ("Finitary " ++ name) do
  prop "is bijection (1)" $
    foreachF \(_ ∷ Proxy a) →
    foreachF \(_ ∷ Proxy b) →
    foreach  \(x ∷ f a b) →
      decode (encode x) == x
  prop "is bijection (2)" $
    foreachF \(_ ∷ Proxy a) →
    foreachF \(_ ∷ Proxy b) →
    foreach  \(Index x ∷ Index (f a b)) →
      encode (decode x ∷ f a b) == x
  prop "respects comparison" $
    foreachF \(_ ∷ Proxy a) →
    foreachF \(_ ∷ Proxy b) →
    foreach  \(x ∷ f a b) →
    foreach  \(y ∷ f a b) →
      compare x y == compare (encode x) (encode y)
