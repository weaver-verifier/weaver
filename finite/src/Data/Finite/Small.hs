{-# LANGUAGE
    DataKinds,
    FlexibleContexts,
    FlexibleInstances,
    KindSignatures,
    MonoLocalBinds,
    TemplateHaskell,
    TypeOperators,
    UndecidableInstances,
    UnicodeSyntax
  #-}

module Data.Finite.Small (MaxSmallSize, Small, fromInt, toInt) where

import Data.Finite.Class (Finitary (..))
import GHC.TypeLits (Nat, type (-))
import Language.Haskell.TH (Type (..), TyLit (..))

-- | The maximum size that a 'Small' type is allowed to have.
type MaxSmallSize = $(pure (LitT (NumTyLit (toInteger (maxBound ∷ Int) + 1))))

-- | The class of "small" finite types (i.e. types that can fit in a
-- non-negative Int).
class    (Finitary a, IsZero (Size a - MaxSmallSize)) ⇒ Small a where
instance (Finitary a, IsZero (Size a - MaxSmallSize)) ⇒ Small a where

class    IsZero (a ∷ Nat) where
instance IsZero 0         where

fromInt ∷ Small a ⇒ Int → a
fromInt = decode . fromIntegral

toInt ∷ Small a ⇒ a → Int
toInt = fromIntegral . encode
