{-# LANGUAGE
    BlockArguments,
    ConstraintKinds,
    DataKinds,
    FlexibleContexts,
    RankNTypes,
    ScopedTypeVariables,
    TypeFamilies,
    TypeOperators,
    UndecidableInstances,
    UnicodeSyntax
  #-}

module Data.Finite.Container (
  Container, Index,
  lookup, reify
) where

import           Prelude hiding (lookup)
import           Data.Finite.Class (Finitary (..))
import           Data.Finite.Internal (Finite (..))
import           Data.Finite.Small (Small, MaxSmallSize)
import           Data.Proxy (Proxy (..))
import           Data.Reflection (Reifies (..), reifyNat)
import qualified Data.Reflection as R
import           Data.Traversable (mapAccumL)
import           Data.Type.Equality ((:~:) (..))
import           Data.Vector (Vector, (!), fromList)
import           GHC.TypeNats (KnownNat, type (-))
import           Unsafe.Coerce (unsafeCoerce)

-- | The class of type-level containers containing elements of type @a@.
type Container c a = (KnownNat (Size c), Small (Index c), Reifies c (Vector a))

-- | The type of indices into the type-level container @c@.
newtype Index c = Index Int
  deriving (Eq, Ord, Show)

instance Container c a ⇒ Finitary (Index c) where
  type Size (Index c) = Size c
  encode (Index  x) = Finite (fromIntegral x)
  decode (Finite x) = Index  (fromIntegral x)

-- | Obtains the original element.
lookup ∷ Container s a ⇒ Index s → a
lookup (Index x ∷ Index s) = reflect (Proxy ∷ Proxy s) ! x

-- | Reifies a container to the type level.
reify ∷ Traversable f ⇒ f a → (∀ c. Container c a ⇒ f (Index c) → r) → r
reify (xs ∷ f a) k =
  let (w' ∷ Vector a, r') =
        R.reify w' \(_ ∷ Proxy c) →
        reifyNat (fromIntegral (length w')) \(_ ∷ Proxy n) →
          case (unsafeCoerce Refl ∷ '(Size c, n - MaxSmallSize) :~: '(n, 0)) of
            Refl → let acc (i, ys) x = ((i + 1, x:ys), Index i ∷ Index c)
                       ((_, w), r) = mapAccumL acc (0, []) xs
                   in (fromList (reverse w), k r)
  in r'
