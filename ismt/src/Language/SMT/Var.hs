{-# LANGUAGE
    BlockArguments,
    DataKinds,
    GADTs,
    OverloadedLists,
    OverloadedStrings,
    RankNTypes,
    TypeOperators,
    UnicodeSyntax
  #-}

module Language.SMT.Var where

import Data.GADT.Compare (GEq (..), GCompare (..), GOrdering (..), defaultCompare, defaultEq)
import Data.GADT.Show (GShow (..))
import Data.Type.Equality ((:~:) (..))
import Data.Void (Void)
import Language.SMT.SExpr (SExpr (..), SExpressible (..))

data Array a b

class GCompare v ⇒ Var v where
  rank ∷ v a → Rank a

data Sort a where
  Bool    ∷ Sort Bool
  Integer ∷ Sort Integer
  Array   ∷ Sort a → Sort b → Sort (Array a b)

instance Eq (Sort a) where
  (==) = defaultEq

instance Ord (Sort a) where
  compare = defaultCompare

instance Show (Sort a) where
  showsPrec _ Bool = showString "Bool"
  showsPrec _ Integer = showString "Integer"
  showsPrec d (Array x y) = showParen (d > 10) $
    showString "Array " .
    showsPrec 11 x .
    showString " " .
    showsPrec 11 y

instance GEq Sort where
  geq Bool Bool = Just Refl
  geq Integer Integer = Just Refl
  geq (Array x₁ y₁) (Array x₂ y₂) = do
    Refl ← geq x₁ x₂
    Refl ← geq y₁ y₂
    return Refl
  geq _ _ = Nothing

instance GCompare Sort where
  gcompare Bool Bool = GEQ
  gcompare Bool _ = GLT
  gcompare Integer Bool = GGT
  gcompare Integer Integer = GEQ
  gcompare Integer (Array _ _) = GLT
  gcompare (Array x₁ y₁) (Array x₂ y₂) =
    case (gcompare x₁ x₂, gcompare y₁ y₂) of
      (GLT, _)   → GLT
      (GEQ, GLT) → GLT
      (GEQ, GEQ) → GEQ
      (GEQ, GGT) → GGT
      (GGT, _)   → GGT
  gcompare (Array _ _) _ = GGT

instance GShow Sort where
  gshowsPrec = showsPrec

instance SExpressible (Sort a) where
  toSExpr Bool = "Bool"
  toSExpr Integer = "Int"
  toSExpr (Array x y) = ["Array", toSExpr x, toSExpr y]

data Sorts a where
  SNil  ∷ Sorts '[]
  SCons ∷ Sort a → Sorts xs → Sorts (a ': xs)

instance Eq (Sorts a) where
  (==) = defaultEq

instance Ord (Sorts a) where
  compare = defaultCompare

instance GEq Sorts where
  geq SNil SNil = Just Refl
  geq (SCons x₁ xs₁) (SCons x₂ xs₂) = do
    Refl ← geq x₁ x₂
    Refl ← geq xs₁ xs₂
    return Refl
  geq _ _ = Nothing

instance GCompare Sorts where
  gcompare SNil SNil = GEQ
  gcompare SNil (SCons _ _) = GLT
  gcompare (SCons _ _) SNil = GGT
  gcompare (SCons x₁ xs₁) (SCons x₂ xs₂) =
    case (gcompare x₁ x₂, gcompare xs₁ xs₂) of
      (GLT, _)   → GLT
      (GEQ, GLT) → GLT
      (GEQ, GEQ) → GEQ
      (GEQ, GGT) → GGT
      (GGT, _)   → GGT

instance SExpressible (Sorts a) where
  toSExpr = List . go
    where go ∷ Sorts a → [SExpr Void]
          go SNil = []
          go (SCons x xs) = toSExpr x : go xs

data Rank a where
  Rank ∷ Sorts xs → Sort r → Rank '(xs, r)

instance Eq (Rank a) where
  (==) = defaultEq

instance Ord (Rank a) where
  compare = defaultCompare

instance GEq Rank where
  geq (Rank x₁ y₁) (Rank x₂ y₂) = do
    Refl ← geq x₁ x₂
    Refl ← geq y₁ y₂
    return Refl

instance GCompare Rank where
  gcompare (Rank x₁ y₁) (Rank x₂ y₂) =
    case (gcompare x₁ x₂, gcompare y₁ y₂) of
      (GLT, _)   → GLT
      (GEQ, GLT) → GLT
      (GEQ, GEQ) → GEQ
      (GEQ, GGT) → GGT
      (GGT, _)   → GGT
