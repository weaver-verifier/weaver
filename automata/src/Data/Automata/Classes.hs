{-# LANGUAGE BlockArguments, GADTs, UnicodeSyntax #-}

module Data.Automata.Classes where

import           Data.Align (Align (..))
import           Data.Finite.Small (Small)
import qualified Data.Finite.Small.Map as Small
import qualified Data.Map.Lazy as Lazy
import qualified Data.Map.Merge.Lazy as Lazy
import           Data.Key (Key)

class Functor f ⇒ PointedWithKey f where
  singleton ∷ Key f → a → f a

instance Ord k ⇒ PointedWithKey (Lazy.Map k) where
  singleton = Lazy.singleton

instance Small k ⇒ PointedWithKey (Small.Map k) where
  singleton = Small.singleton

class Align f ⇒ Absorb f where
  absorb ∷ f a → f b → f (a, Maybe b)
  absorb = absorbWith (,)

  absorbWith ∷ (a → Maybe b → c) → f a → f b → f c
  absorbWith f x y = fmap (uncurry f) (absorb x y)

  {-# MINIMAL absorb | absorbWith #-}

instance Ord k ⇒ Absorb (Lazy.Map k) where
  absorbWith f = Lazy.merge
    (Lazy.mapMissing \_ x → f x Nothing)
    Lazy.dropMissing
    (Lazy.zipWithMatched \_ x → f x . Just)

instance Ord k ⇒ Absorb (Small.Map k) where
  absorb = Small.absorb
  absorbWith = Small.absorbWith
