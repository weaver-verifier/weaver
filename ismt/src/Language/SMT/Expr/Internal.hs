{-# LANGUAGE
    DataKinds,
    KindSignatures,
    GADTs,
    QuantifiedConstraints,
    UnicodeSyntax
  #-}

module Language.SMT.Expr.Internal where

import Data.Some (Some (..))
import Language.SMT.SExpr (SExpr, SExpressible (..))

newtype Expr (v ∷ ([*], *) → *) a = Expr { getExpr ∷ SExpr (Some v) }
  deriving (Eq, Ord, Show)

instance (∀ b. SExpressible (v b)) ⇒ SExpressible (Expr v a) where
  toSExpr (Expr e) = e >>= \(Some x) → toSExpr x
