{-# LANGUAGE
    BlockArguments,
    FlexibleInstances,
    RankNTypes,
    ScopedTypeVariables,
    TypeApplications,
    TypeSynonymInstances,
    UnicodeSyntax
  #-}

module Data.Automata.Util where

import           Data.Finite (Finite, finites)
import           Data.Finite.Class
import qualified Data.Finite.Set as Set
import qualified Data.Map as Map
import           Data.Maybe (fromJust)
import           Data.Proxy (Proxy (..))
import           Data.Vector.Sized (Vector, fromList)
import           Data.Void (Void)
import           GHC.TypeLits (KnownNat, SomeNat (..), someNatVal, natVal)
import           Test.Hspec (Spec, it)
import           Test.Hspec.LeanCheck (propertyFor)
import           Test.LeanCheck (Listable (..), cons0, cons1, listsOfLength, mapT)
import           Test.LeanCheck.Core (Testable (..))
import           Test.LeanCheck.Function ()
import           Test.LeanCheck.Utils.Types (Map (..), Natural (..), Set (..))

instance Listable Void where
  tiers = []

instance Listable (Proxy k) where
  tiers = cons0 Proxy

instance (Listable a, Eq a, Listable b) ⇒ Listable (Fun a b) where
  tiers = cons1 Fun

instance KnownNat n ⇒ Listable (Finite n) where
  list = finites

instance (Finitary a, Listable a) ⇒ Listable (Set.Set a) where
  tiers = cons1 (\(Set xs) → Set.fromList xs)

instance (KnownNat n, Listable a) ⇒ Listable (Vector n a) where
  tiers = mapT (fromJust . fromList) (listsOfLength (fromIntegral (natVal (Proxy @n))) tiers)

instance (Ord a, Listable a, Listable b) ⇒ Listable (Map.Map a b) where
  tiers = cons1 (\(Map xs) → Map.fromList xs)

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

prop ∷ Testable a ⇒ String → a → Spec
prop xs p = it xs (propertyFor 10000 p)

splits ∷ [a] → [([a], [a])]
splits []     = [([], [])]
splits (x:xs) = ([], x:xs) : do
  (l, r) ← splits xs
  return (x:l, r)

parts ∷ [a] → [[[a]]]
parts []     = [[]]
parts [c]    = [[[c]]]
parts (c:cs) = do
  p:ps ← parts cs
  [(c:p):ps, [c]:p:ps]

separations ∷ [a] → [([a], [a])]
separations [] = [([], [])]
separations (x:xs) = do
  (l, r) ← separations xs
  [(x:l, r), (l, x:r)]
