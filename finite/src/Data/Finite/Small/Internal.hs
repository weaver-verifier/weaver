{-# LANGUAGE
    DeriveTraversable,
    GeneralizedNewtypeDeriving,
    TypeFamilies,
    UnicodeSyntax
  #-}

module Data.Finite.Small.Internal where

import Prelude hiding (lookup)
import Data.Align (Align)
import Data.Finite.Small (Small, fromInt, toInt)
import Data.Functor.Bind (Apply (..), Bind (..))
import Data.Functor.Plus (Alt (..), Plus (..))
import Data.IntMap (IntMap)
import Data.IntSet (IntSet)
import Data.Key (Key, Keyed (..), Lookup (..), Indexable (..), FoldableWithKey (..))

-- | A set of 'Small' 'Finitary' type @a@.
--
-- This is internally represented as an 'IntSet'.
newtype Set a = Set IntSet
  deriving (Eq, Ord)

-- | A map from 'Small' 'Finitary' type @k@ to @a@.
--
-- This is internally represented as an 'IntMap'.
newtype Map k a = Map (IntMap a)
  deriving (Align, Apply, Bind, Eq, Foldable, Functor, Ord, Plus, Traversable)

instance Small k ⇒ FoldableWithKey (Map k) where
  foldrWithKey f z (Map xs) = foldrWithKey (f . fromInt) z xs

type instance Key (Map k) = k

instance Small k ⇒ Lookup (Map k) where
  lookup k (Map m) = lookup (toInt k) m

instance Small k ⇒ Indexable (Map k) where
  index (Map m) k = index m (toInt k)

instance Alt (Map k) where
  Map m₁ <!> Map m₂ = Map (m₁ <!> m₂)

instance Small k ⇒ Keyed (Map k) where
  mapWithKey f (Map m) = Map (mapWithKey (f . fromInt) m)
