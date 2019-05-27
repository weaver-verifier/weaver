{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# LANGUAGE
    DataKinds,
    PatternSynonyms,
    ScopedTypeVariables,
    TypeApplications,
    TypeFamilies,
    TypeOperators,
    UndecidableInstances,
    UnicodeSyntax
  #-}

module Data.Finite.Set (
  Set (..),
  member, isEmpty,
  isSubsetOf,
  empty, universe, singleton,
  insert, delete,
  union, unions,
  intersection, intersections,
  difference, complement,
  mapJust,
  mapLeft, mapRight,
  mapThis, mapThat,
  mapStrongFst, mapStrongSnd,
  cartesianProduct,
  toList, fromList,
  map, bind,
  foldMap, traverse
) where

import           Prelude hiding (foldMap, map, traverse)
import qualified Prelude
import           Data.Bits ((.&.), (.|.), bit, clearBit, setBit, shiftL, testBit)
import qualified Data.Bits as Bits
import           Data.Finite.Class (Finitary (..), size)
import           Data.Finite.Internal (Finite (..))
import           Data.Foldable (foldl')
import           Data.These (These)
import           GHC.TypeNats (type (^))

-- | Sets of finite elements, represented as a bit set.
newtype Set a = Set (Finite (2 ^ Size a))
  deriving (Eq, Ord)

instance Semigroup (Set a) where
  (<>) = union

instance Monoid (Set a) where
  mempty = empty

instance (Finitary a, Show a) ⇒ Show (Set a) where
  show xs = "fromList " ++ show (toList xs)

instance Finitary a ⇒ Finitary (Set a) where
  type Size (Set a) = 2 ^ Size a
  encode (Set x) = x
  decode = Set

{-# COMPLETE Set' #-}
pattern Set' ∷ Integer → Set a
pattern Set' x = Set (Finite x)

member ∷ Finitary a ⇒ a → Set a → Bool
member x (Set' xs) = testBit xs (fromIntegral (encode x))

isEmpty ∷ Set a → Bool
isEmpty (Set' xs) = xs == 0

isSubsetOf ∷ Set a → Set a → Bool
isSubsetOf x y = isEmpty (difference x y)

empty ∷ Set a
empty = Set' 0

universe ∷ ∀ a. Finitary a ⇒ Set a
universe = Set' (2 ^ (size @a ∷ Integer) - 1)

singleton ∷ Finitary a ⇒ a → Set a
singleton = Set' . bit . fromIntegral . encode

insert ∷ Finitary a ⇒ a → Set a → Set a
insert x (Set' xs) = Set' (setBit xs (fromIntegral (encode x)))

delete ∷ Finitary a ⇒ a → Set a → Set a
delete x (Set' xs) = Set' (clearBit xs (fromIntegral (encode x)))

union ∷ Set a → Set a → Set a
union (Set' xs) (Set' ys) = Set' (xs .|. ys)

unions ∷ Foldable f ⇒ f (Set a) → Set a
unions = foldl' union empty

intersection ∷ Set a → Set a → Set a
intersection (Set' xs) (Set' ys) = Set' (xs .&. ys)

intersections ∷ (Finitary a, Foldable f) ⇒ f (Set a) → Set a
intersections = foldl' intersection universe

difference ∷ Set a → Set a → Set a
difference (Set' xs) (Set' ys) = Set' (xs .&. Bits.complement ys)

complement ∷ Finitary a ⇒ Set a → Set a
complement = difference universe

mapJust ∷ Set a → Set (Maybe a)
mapJust (Set' xs) = Set' (shiftL xs 1)

mapLeft ∷ Set a → Set (Either a b)
mapLeft (Set' xs) = Set' xs

mapRight ∷ ∀ a b. Finitary a ⇒ Set b → Set (Either a b)
mapRight (Set' xs) = Set' (shiftL xs (size @a))

mapThis ∷ Set a → Set (These a b)
mapThis (Set' xs) = Set' xs

mapThat ∷ ∀ a b. Finitary a ⇒ Set b → Set (These a b)
mapThat (Set' xs) = Set' (shiftL xs (size @a))

mapStrongFst ∷ ∀ a b. (Finitary a, Finitary b) ⇒ a → Set b → Set (a, b)
mapStrongFst x (Set' xs) = Set' (shiftL xs (size @b * fromIntegral (encode x)))

mapStrongSnd ∷ (Finitary a, Finitary b) ⇒ Set a → b → Set (a, b)
mapStrongSnd xs y = cartesianProduct xs (Set' (bit (fromIntegral (encode y))))

cartesianProduct ∷ ∀ a b. (Finitary a, Finitary b) ⇒ Set a → Set b → Set (a, b)
cartesianProduct (Set' xs) (Set' ys) = Set (Finite (foldl' go 0 [0..size @a]))
  where go z i | testBit xs i = shiftL ys (i * size @b) .|. z
               | otherwise    = z

toList ∷ Finitary a ⇒ Set a → [a]
toList (Set' n) = go 0
  where go i | n < 2 ^ i   = []
             | testBit n i = decode (Finite (fromIntegral i)) : go (i + 1)
             | otherwise   = go (i + 1)

fromList ∷ Finitary a ⇒ [a] → Set a
fromList = foldl' (flip insert) empty

map ∷ (Finitary a, Finitary b) ⇒ (a → b) → Set a → Set b
map f = fromList . fmap f . toList

bind ∷ (Finitary a, Finitary b) ⇒ (a → Set b) → Set a → Set b
bind f = fromList . (>>= toList . f) . toList

foldMap ∷ (Finitary a, Monoid m) ⇒ (a → m) → Set a → m
foldMap f = Prelude.foldMap f . toList

traverse ∷ (Finitary a, Finitary b, Applicative f) ⇒ (a → f b) → Set a → f (Set b)
traverse f = fmap fromList . Prelude.traverse f . toList
