{-# LANGUAGE
    DeriveTraversable,
    GeneralizedNewtypeDeriving,
    TypeFamilies,
    UnicodeSyntax
  #-}

module Data.Finite.Small.Set (
  Set, member,
  empty, singleton, insert, delete,
  union, intersection, difference,
) where

import           Prelude hiding (lookup)
import           Data.Finite.Small (Small, toInt)
import           Data.Finite.Small.Internal (Set (..))
import qualified Data.IntSet as IntSet

member ∷ Small a ⇒ a → Set a → Bool
member k (Set m) = IntSet.member (toInt k) m

empty ∷ Small a ⇒ Set a
empty = Set IntSet.empty

singleton ∷ Small a ⇒ a → Set a
singleton k = Set (IntSet.singleton (toInt k))

insert ∷ Small a ⇒ a → Set a → Set a
insert k (Set m) = Set (IntSet.insert (toInt k) m)

delete ∷ Small a ⇒ a → Set a → Set a
delete k (Set m) = Set (IntSet.delete (toInt k) m)

union ∷ Set a → Set a → Set a
union (Set m₁) (Set m₂) = Set (IntSet.union m₁ m₂)

intersection ∷ Set a → Set a → Set a
intersection (Set m₁) (Set m₂) = Set (IntSet.intersection m₁ m₂)

difference ∷ Set a → Set a → Set a
difference (Set m₁) (Set m₂) = Set (IntSet.difference m₁ m₂)
