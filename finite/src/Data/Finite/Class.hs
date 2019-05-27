{-# OPTIONS_GHC
    -fplugin GHC.TypeLits.KnownNat.Solver
    -fplugin GHC.TypeLits.Normalise
  #-}
{-# LANGUAGE
    AllowAmbiguousTypes,
    ApplicativeDo,
    BangPatterns,
    DataKinds,
    FlexibleContexts,
    GeneralizedNewtypeDeriving,
    NoStarIsType,
    PolyKinds,
    ScopedTypeVariables,
    TypeApplications,
    TypeFamilies,
    TypeOperators,
    UndecidableInstances,
    UnicodeSyntax
  #-}

module Data.Finite.Class where

import Control.Monad.Trans.State (evalState, get, put)
import Data.Bifunctor (bimap)
import Data.Finite ( finites, combineSum, separateSum
                   , combineProduct, separateProduct
                   , shift, unshift
                   )
import Data.Finite.Internal (Finite (..), getFinite)
import Data.Foldable (Foldable (..))
import Data.Function (on)
import Data.Functor.Identity (Identity (..))
import Data.Key ( Key, Lookup, Keyed, Zip, ZipWithKey, Indexable
                , FoldableWithKey (..), TraversableWithKey (..)
                )
import Data.List (intercalate)
import Data.Proxy (Proxy (..))
import Data.These (These (..), these)
import Data.Tuple (swap)
import Data.Vector ((!), fromList, replicateM)
import Data.Void (Void, absurd)
import GHC.TypeLits (KnownNat, Nat, type (+), type (*), type (^), natVal)

-- | The class of finite types. Instances must satisfy the following laws:
--
-- prop> encode . decode == id
-- prop> decode . encode == id
-- prop> compare x y == compare (encode x) (encode y)
class (KnownNat (Size a), Ord a) ⇒ Finitary a where
  type Size a ∷ Nat
  encode ∷ a → Finite (Size a)
  decode ∷ Finite (Size a) → a

-- | Returns the size of a type as an 'Integral' value.
size ∷ ∀ a b. (Finitary a, Integral b) ⇒ b
size = fromIntegral (natVal (Proxy @(Size a)))

-- | The list of all elements of a finite type.
--
-- The elements are sorted and unique.
universe ∷ Finitary a ⇒ [a]
universe = map decode finites

-- | Memoizes a function over a finite type.
memoize ∷ Finitary a ⇒ (a → b) → (a → b)
memoize f = runIdentity (memoizeF (Identity . f))

-- | Memoizes an effectful function over a finite type.
--
-- This is 'sequenceA' for functions.
memoizeF ∷ (Applicative f, Finitary a) ⇒ (a → f b) → f (a → b)
memoizeF f = do
  vec ← fromList <$> traverse f universe
  return (\x → vec ! fromIntegral (getFinite (encode x)))

-- | A default implementation of '(==)' for finite types.
defaultEquals ∷ Finitary a ⇒ a → a → Bool
defaultEquals = (==) `on` encode

-- | A default implementation of 'compare' for finite types.
defaultCompare ∷ Finitary a ⇒ a → a → Ordering
defaultCompare = compare `on` encode

instance Finitary Void where
  type Size Void = 0
  encode = absurd
  decode x = x `seq` error "decode: invalid Finite"

instance Finitary () where
  type Size () = 1
  encode () = 0
  decode x  = x `seq` ()

instance Finitary (Proxy k) where
  type Size (Proxy k) = 1
  encode Proxy = 0
  decode x     = x `seq` Proxy

instance Finitary Bool where
  type Size Bool = 2
  encode False = 0
  encode True  = 1
  decode x     = x == 1

instance Finitary a ⇒ Finitary (Maybe a) where
  type Size (Maybe a) = 1 + Size a
  encode = maybe 0 (shift . encode)
  decode = fmap decode . unshift

instance (Finitary a, Finitary b) ⇒ Finitary (Either a b) where
  type Size (Either a b) = Size a + Size b
  encode = combineSum . bimap encode encode
  decode = bimap decode decode . separateSum

instance (Finitary a, Finitary b) ⇒ Finitary (a, b) where
  type Size (a, b) = Size a * Size b
  encode = combineProduct . swap . bimap encode encode
  decode = bimap decode decode . swap . separateProduct

instance (Finitary a, Finitary b) ⇒ Finitary (These a b) where
  type Size (These a b) = Size a + Size b + Size a * Size b
  encode = encode . these (Left . Left) (Left . Right) (curry Right)
  decode = either (either This That) (uncurry These) . decode

instance KnownNat n ⇒ Finitary (Finite n) where
  type Size (Finite n) = n
  encode = id
  decode = id

-- | Functions with a finite domain populate a number of typeclasses.
newtype Fun a b = Fun { getFun ∷ a → b }
  deriving ( Applicative, Functor, Indexable
           , Keyed, Lookup, Monad, Monoid
           , Semigroup, Zip, ZipWithKey
           )

type instance Key (Fun a) = a

instance (Finitary a, Show a, Show b) ⇒ Show (Fun a b) where
  show (Fun f) =
    "(\\case {" ++
    intercalate "; " (map (\x → show x ++ " -> " ++ show (f x)) universe) ++
    "})"

instance (Finitary a, Eq b) ⇒ Eq (Fun a b) where
  Fun f == Fun g = all (\x → f x == g x) universe

instance (Finitary a, Ord b) ⇒ Ord (Fun a b) where
  compare (Fun f) (Fun g) = compare (map f runiverse) (map g runiverse)
    where runiverse = reverse universe

instance Finitary a ⇒ Foldable (Fun a) where
  fold (Fun f) = foldMap f universe
  foldMap f (Fun g) = foldMap (f . g) universe
  foldr f z (Fun g) = foldr (f . g) z universe
  foldr' f z (Fun g) = foldr' (f . g) z universe
  toList (Fun f) = map f universe
  null _ = size @a == (0 ∷ Integer)
  length _ = size @a

instance Finitary a ⇒ Traversable (Fun a) where
  sequenceA (Fun f) = Fun <$> memoizeF f

instance Finitary a ⇒ FoldableWithKey (Fun a) where
  foldMapWithKey f (Fun g) = foldMap (\x → f x (g x)) universe
  foldrWithKey f z (Fun g) = foldr (\x → f x (g x)) z universe

instance Finitary a ⇒ TraversableWithKey (Fun a) where
  traverseWithKey f (Fun g) = Fun <$> memoizeF (\x → f x (g x))

instance (Finitary a, Finitary b) ⇒ Finitary (Fun a b) where
  type Size (Fun a b) = Size b ^ Size a
  encode (Fun f) = combinePower (encode . f . decode)
  decode i = Fun (decode . separatePower i . encode)

-- | Function space over finite sets.
combinePower ∷ ∀ n b. (KnownNat n, KnownNat b) ⇒ (Finite n → Finite b) → Finite (b ^ n)
combinePower f = Finite (go 0 1) where
  go !i !p | i == n    = 0
           | otherwise = p * x + go (i + 1) (p * b)
           where n = natVal (Proxy @n)
                 b = natVal (Proxy @b)
                 x = getFinite (f (Finite i))

-- | Take a function space apart.
separatePower ∷ ∀ n b. (KnownNat n, KnownNat b) ⇒ Finite (b ^ n) → Finite n → Finite b
separatePower (Finite f) = (v !) . fromIntegral
  where v = evalState (replicateM (fromIntegral n) go) f
        n = natVal (Proxy @n)
        b = natVal (Proxy @b)
        go = do
          p ← get
          let (d, r) = divMod p b
          put d
          pure (Finite r)
