{-# OPTIONS_GHC
    -fno-warn-orphans
    -fplugin GHC.TypeLits.KnownNat.Solver
  #-}
{-# LANGUAGE
    DerivingVia,
    StandaloneDeriving,
    UndecidableInstances,
    UnicodeSyntax
  #-}

module Data.Finite.Instances where

import Data.Finite.Class (Finitary (..), Fun (..), memoizeF)
import Data.Key (FoldableWithKey , TraversableWithKey (..))

deriving via Fun a b instance (Finitary a, Eq b) ⇒ Eq (a → b)
deriving via Fun a b instance (Finitary a, Ord b) ⇒ Ord (a → b)
deriving via Fun a b instance (Finitary a, Finitary b) ⇒ Finitary (a → b)
deriving via Fun a   instance Finitary a ⇒ Foldable ((→) a)
deriving via Fun a   instance Finitary a ⇒ FoldableWithKey ((→) a)

instance Finitary a ⇒ Traversable ((→) a) where
  traverse f g = memoizeF (f . g)

instance Finitary a ⇒ TraversableWithKey ((→) a) where
  traverseWithKey f g = memoizeF (\x → f x (g x))
