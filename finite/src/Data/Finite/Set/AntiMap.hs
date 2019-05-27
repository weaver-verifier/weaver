{-# LANGUAGE ApplicativeDo, BlockArguments, DeriveTraversable, UnicodeSyntax #-}

module Data.Finite.Set.AntiMap (
  AntiMap,
  isEmpty, member, lookup,
  toList, fromList, fromListWith,
  empty, universe, singleton,
  insert, insertWith,
  union, unionWith,
  unions, unionsWith,
  intersection, intersectionWith,
  intersections, intersectionsWith
) where

import           Prelude hiding (lookup)
import           Data.Finite.Class (Finitary)
import           Data.Finite.Set (Set, isSubsetOf)
import qualified Data.Finite.Set as Set
import           Data.List (find)
import           Data.Maybe (isJust)

newtype AntiMap k a = AntiMap [(Set k, a)]
  deriving (Eq, Functor, Ord)

instance (Finitary k, Show k, Show a) ⇒ Show (AntiMap k a) where
  show (AntiMap xss) = "fromList " ++ show xss

isEmpty ∷ AntiMap k a → Bool
isEmpty = null . toList

member ∷ Set k → AntiMap k a → Bool
member xs = isJust . lookup xs

lookup ∷ Set k → AntiMap k a → Maybe a
lookup xs = fmap snd . find (isSubsetOf xs . fst) . toList

toList ∷ AntiMap k a → [(Set k, a)]
toList (AntiMap xss) = xss

fromList ∷ [(Set k, a)] → AntiMap k a
fromList = foldr (uncurry insert) empty

fromListWith ∷ (a → a → a) → [(Set k, a)] → AntiMap k a
fromListWith f = foldr (uncurry (insertWith f)) empty

empty ∷ AntiMap k a
empty = AntiMap []

universe ∷ Finitary k ⇒ a → AntiMap k a
universe x = AntiMap [(Set.universe, x)]

singleton ∷ Set k → a → AntiMap k a
singleton xs x = AntiMap [(xs, x)]

insert ∷ Set k → a → AntiMap k a → AntiMap k a
insert = insertWith const

insertWith ∷ (a → a → a) → Set k → a → AntiMap k a → AntiMap k a
insertWith f xs v = AntiMap . go . toList
  where go [] = [(xs, v)]
        go yss'@(ys'@(ys, v'):yss) =
          case compare xs ys of
            GT → if isSubsetOf ys xs
                 then go yss
                 else ys' : go yss
            EQ → (ys, f v v') : yss
            LT → if any (isSubsetOf xs . fst) yss'
                 then yss'
                 else (xs, v) : yss'

union ∷ AntiMap k a → AntiMap k a → AntiMap k a
union = unionWith const

unionWith ∷ (a → a → a) → AntiMap k a → AntiMap k a → AntiMap k a
unionWith f (AntiMap xss') (AntiMap yss') = AntiMap (go xss' yss')
  where go xss [] = xss
        go [] yss = yss
        go (xs'@(xs, v):xss) (ys'@(ys, w):yss) =
          case compare xs ys of
            LT → if any (isSubsetOf xs . fst) (ys':yss)
                 then go xss (ys':yss)
                 else xs' : go xss (ys':yss)
            GT → if any (isSubsetOf ys . fst) (xs':xss)
                 then go (xs':xss) yss
                 else ys' : go (xs':xss) yss
            EQ → (xs, f v w) : go xss yss

unions ∷ Foldable f ⇒ f (AntiMap k a) → AntiMap k a
unions = foldr union empty

unionsWith ∷ Foldable f ⇒ (a → a → a) → f (AntiMap k a) → AntiMap k a
unionsWith f = foldr (unionWith f) empty

intersection ∷ AntiMap k a → AntiMap k a → AntiMap k a
intersection = intersectionWith const

intersectionWith ∷ (a → b → c) → AntiMap k a → AntiMap k b → AntiMap k c
intersectionWith f xss yss = fromList do
  (xs, v) ← toList xss
  (ys, w) ← toList yss
  pure (Set.intersection xs ys, f v w)

intersections ∷ (Finitary k, Foldable f) ⇒ a → f (AntiMap k a) → AntiMap k a
intersections = intersectionsWith const

intersectionsWith ∷ (Finitary k, Foldable f) ⇒ (a → r → r) → r → f (AntiMap k a) → AntiMap k r
intersectionsWith f x = foldr (intersectionWith f) (universe x)
