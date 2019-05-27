{-# LANGUAGE UnicodeSyntax #-}

module Language.SMT.Backend.Hybrid where

import Language.SMT.Backend

hybrid ∷ IO Backend → IO Backend → IO Backend
hybrid sat int = do
  backend₁ ← sat
  backend₂ ← int
  return Backend
    { backendDeclare = \x p r → do
        backendDeclare backend₁ x p r
        backendDeclare backend₂ x p r
    , backendSatisfiable = backendSatisfiable backend₁
    , backendInterpolate = backendInterpolate backend₂
    }
