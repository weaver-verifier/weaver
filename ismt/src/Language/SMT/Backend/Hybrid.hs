{-# LANGUAGE UnicodeSyntax #-}

module Language.SMT.Backend.Hybrid where

import Language.SMT.Backend

hybrid ∷ (Maybe FilePath → IO Backend) → (Maybe FilePath → IO Backend) → (Maybe FilePath → IO Backend)
hybrid sat int script = do
  backend₁ ← sat script
  backend₂ ← int script
  return Backend
    { backendDeclare = \x p r → do
        backendDeclare backend₁ x p r
        backendDeclare backend₂ x p r
    , backendSatisfiable = backendSatisfiable backend₁
    , backendInterpolate = backendInterpolate backend₂
    }
