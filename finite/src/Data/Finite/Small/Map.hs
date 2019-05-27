{-# LANGUAGE
    DeriveTraversable,
    GeneralizedNewtypeDeriving,
    TypeFamilies,
    UnicodeSyntax
  #-}

module Data.Finite.Small.Map (
  Map, member, lookup,
  empty, singleton,
  insert, delete,
  union, unionWith,
  intersection, intersectionWith,
  difference, differenceWith,
  absorb, absorbWith,
  fromList, fromListWith,
  keys, keysSet
) where

import           Prelude hiding (lookup)
import           Data.Bifunctor (first)
import           Data.Finite.Small (Small, fromInt, toInt)
import           Data.Finite.Small.Internal (Map (..), Set (..))
import qualified Data.IntMap as IntMap
import qualified Data.Key as Key

member ∷ Small k ⇒ k → Map k a → Bool
member k (Map m) = IntMap.member (toInt k) m

lookup ∷ Small k ⇒ k → Map k a → Maybe a
lookup = Key.lookup

empty ∷ Map k a
empty = Map IntMap.empty

singleton ∷ Small k ⇒ k → a → Map k a
singleton k v = Map (IntMap.singleton (toInt k) v)

insert ∷ Small k ⇒ k → a → Map k a → Map k a
insert k v (Map m) = Map (IntMap.insert (toInt k) v m)

delete ∷ Small k ⇒ k → Map k a → Map k a
delete k (Map m) = Map (IntMap.delete (toInt k) m)

union ∷ Map k a → Map k a → Map k a
union (Map m₁) (Map m₂) = Map (IntMap.union m₁ m₂)

unionWith ∷ (a → a → a) → Map k a → Map k a → Map k a
unionWith f (Map m₁) (Map m₂) = Map (IntMap.unionWith f m₁ m₂)

intersection ∷ Map k a → Map k a → Map k a
intersection (Map m₁) (Map m₂) = Map (IntMap.intersection m₁ m₂)

intersectionWith ∷ (a → b → c) → Map k a → Map k b → Map k c
intersectionWith f (Map m₁) (Map m₂) = Map (IntMap.intersectionWith f m₁ m₂)

difference ∷ Map k a → Map k b → Map k a
difference (Map m₁) (Map m₂) = Map (IntMap.difference m₁ m₂)

differenceWith ∷ (a → b → Maybe a) → Map k a → Map k b → Map k a
differenceWith f (Map m₁) (Map m₂) = Map (IntMap.differenceWith f m₁ m₂)

absorb ∷ Map k a → Map k b → Map k (a, Maybe b)
absorb = absorbWith (,)

absorbWith ∷ (a → Maybe b → c) → Map k a → Map k b → Map k c
absorbWith f (Map m₁) (Map m₂) = Map (IntMap.mergeWithKey
  (\_ x y → Just (f x (Just y)))
  (fmap (\x → f x Nothing))
  (\_ → IntMap.empty)
  m₁
  m₂)

fromList ∷ Small k ⇒ [(k, v)] → Map k v
fromList xs = Map (IntMap.fromList (map (first toInt) xs))

fromListWith ∷ Small k ⇒ (v → v → v) → [(k, v)] → Map k v
fromListWith f xs = Map (IntMap.fromListWith f (map (first toInt) xs))

keys ∷ Small k ⇒ Map k a → [k]
keys (Map m) = map fromInt (IntMap.keys m)

keysSet ∷ Map k a → Set k
keysSet (Map m) = Set (IntMap.keysSet m)
