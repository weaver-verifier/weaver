{-# LANGUAGE
    BlockArguments,
    DeriveTraversable,
    FlexibleContexts,
    GADTs,
    ImplicitParams,
    LambdaCase,
    OverloadedStrings,
    PatternSynonyms,
    RankNTypes,
    RecordWildCards,
    ScopedTypeVariables,
    TupleSections,
    TypeOperators,
    UnicodeSyntax,
    ViewPatterns
  #-}

module Weaver.Bound (Bound (..), bounded) where

import Prelude hiding (lookup)
import Control.Monad.State (evalState, get, modify')
import Data.Finite.Container (Container, lookup)
import Data.Function (on)
import Data.List (sortBy)
import Data.Key (toKeyedList)
import Data.Traversable (for)
import Numeric.Natural (Natural)
import Weaver.Counterexample (Counterexample (..), getCex, indeps)
import Weaver.Config
import Weaver.Program (Tag, compareIndep)
import Weaver.Stmt (Stmt)

data Bound
  = NoBound
  | BoundLeft Natural
  | BoundRight Natural
  | BoundMiddle Natural
  | BoundUniform Natural
  | BoundAzadeh Natural
  | BoundRoundRobin

bounded ∷ (Container c ([Tag], Stmt), ?config ∷ Config) ⇒ Bound → Counterexample c → [[Stmt]]
bounded NoBound          = getCex
bounded (BoundLeft n)    = selectLeft    (fromIntegral n)
bounded (BoundRight n)   = selectRight   (fromIntegral n)
bounded (BoundMiddle n)  = selectMiddle  (fromIntegral n) . getCex
bounded (BoundAzadeh n)  = selectAzadeh  (fromIntegral n) . getCex
bounded (BoundUniform n) = selectUniform (fromIntegral n) . getCex
bounded BoundRoundRobin  = selectRoundRobin

selectLeft ∷ (Container c ([Tag], Stmt), ?config ∷ Config) ⇒ Int → Counterexample c → [[Stmt]]
selectLeft n cex = evalState (go cex) 0
  where go Nil = do
          modify' (+ 1)
          return [[]]
        go (Cons c m) =
          (indeps c ++) . concat <$> for (toKeyedList m) \(k, v) → do
            i ← get
            if i < n then
              map (snd (lookup k):) <$> go v
            else
              return []

selectRight ∷ (Container c ([Tag], Stmt), ?config ∷ Config) ⇒ Int → Counterexample c → [[Stmt]]
selectRight n cex = evalState (go cex) 0
  where go Nil = do
          modify' (+ 1)
          return [[]]
        go (Cons c m) =
          (indeps c ++) . concat <$> for (reverse (toKeyedList m)) \(k, v) → do
            i ← get
            if i < n then
              map (snd (lookup k):) <$> go v
            else
              return []

selectRoundRobin ∷ (Container c ([Tag], Stmt), ?config ∷ Config) ⇒ Counterexample c → [[Stmt]]
selectRoundRobin = go []
  where go _ Nil = [[]]
        go x (Cons c m) = indeps c ++
            case dropWhile ((/= LT) . compareIndep x . fst . lookup . fst) ps of
              (k, v):_ → map (snd (lookup k):) (go (fst (lookup k)) v)
              _        → case ps of
                           []       → []
                           (k, v):_ → map (snd (lookup k):) (go (fst (lookup k)) v)
          where ps = sortBy (compareIndep `on` fst . lookup . fst) (toKeyedList m)

selectMiddle ∷ Int → [a] → [a]
selectMiddle n xs = take n₁ (reverse b) ++ take n₂ a
  where l = length xs
        (b, a) = splitAt (l `div` 2) xs
        n₁ = n `div` 2
        n₂ = n - n₁

selectUniform ∷ Int → [a] → [a]
selectUniform _ []     = []
selectUniform 0 _      = []
selectUniform 1 (x:_)  = [x]
selectUniform n (hd:tl) = hd : go r tl
  where (d, r) = length tl `divMod` (n - 1)
        go _ [] = []
        go i xs = last b : go (i - 1) a
          where (b, a) = splitAt (if i > 0 then d + 1 else d) xs

selectAzadeh ∷ Int → [a] → [a]
selectAzadeh n xs = take n₁ (reverse a) ++ take n₁ b ++ take n₁ (reverse b) ++ take n₂ c
  where l = length xs
        (a, ys) = splitAt (l `div` 3) xs
        (b, c)  = splitAt (l `div` 3) ys
        n₁ = n `div` 4
        n₂ = n - n₁ * 3
