{-# LANGUAGE UnicodeSyntax #-}

module Data.Finite.Set.Antichain (
  Antichain,
  isEmpty, member,
  toList, fromList,
  empty, universe, singleton,
  insert, tryInsert,
  union, unions,
  reduce,
  intersection, intersections
) where

import           Data.Finite.Class (Finitary)
import           Data.Finite.Set (Set, isSubsetOf)
import qualified Data.Finite.Set as Set
import           Data.Maybe (fromMaybe)

-- | A compact representation of a downwards-closed set of 'Set's.
newtype Antichain a = Antichain [Set a]
  deriving (Eq, Ord)

instance (Finitary a, Show a) ⇒ Show (Antichain a) where
  show (Antichain xss) = "fromList " ++ show xss

isEmpty ∷ Antichain a → Bool
isEmpty = null . toList

member ∷ Set a → Antichain a → Bool
member xs = any (isSubsetOf xs) . toList

toList ∷ Antichain a → [Set a]
toList (Antichain xss) = xss

fromList ∷ [Set a] → Antichain a
fromList = foldr insert empty

empty ∷ Antichain a
empty = Antichain []

universe ∷ Finitary a ⇒ Antichain a
universe = Antichain [Set.universe]

singleton ∷ Set a → Antichain a
singleton xs = Antichain [xs]

insert ∷ Set a → Antichain a → Antichain a
insert xs xss = fromMaybe xss (tryInsert xs xss)

tryInsert ∷ Set a → Antichain a → Maybe (Antichain a)
tryInsert xs = fmap Antichain . go . toList
  where go [] = Just [xs]
        go yss'@(ys:yss)
          | xs > ys   = if isSubsetOf ys xs
                        then go yss
                        else fmap (ys :) (go yss)
          | otherwise = if any (isSubsetOf xs) yss'
                        then Nothing
                        else Just (xs : yss')

union ∷ Antichain a → Antichain a → Antichain a
union (Antichain xss') (Antichain yss') = Antichain (go xss' yss')
  where go xss [] = xss
        go [] yss = yss
        go (xs:xss) (ys:yss) =
          case compare xs ys of
            LT → if any (isSubsetOf xs) (ys:yss)
                 then go xss (ys:yss)
                 else xs : go xss (ys:yss)
            GT → if any (isSubsetOf ys) (xs:xss)
                 then go (xs:xss) yss
                 else ys : go (xs:xss) yss
            EQ → xs : go xss yss

unions ∷ Foldable f ⇒ f (Antichain a) → Antichain a
unions = foldr union empty

reduce ∷ Set a → Antichain a → Antichain a
reduce xs = fromList . map (Set.intersection xs) . toList

intersection ∷ Antichain a → Antichain a → Antichain a
intersection xss yss = fromList (Set.intersection <$> toList xss <*> toList yss)

intersections ∷ (Foldable f, Finitary a) ⇒ f (Antichain a) → Antichain a
intersections = foldr intersection universe
