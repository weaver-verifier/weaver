{-# LANGUAGE
    LambdaCase,
    OverloadedLists,
    OverloadedStrings,
    RecordWildCards,
    UnicodeSyntax
  #-}

module Language.SMT.Backend.Z3 where

import Data.List.NonEmpty (NonEmpty (..))
import Language.SMT.Backend
import Language.SMT.SExpr

z3 ∷ IO Backend
z3 = do
  (send, recv) ← openPipe "z3" ["-in"] Nothing

  let backendDeclare x ps r = send ["declare-fun", x, ps, r]

      backendSatisfiable e = do
        send ["push"]
        send ["assert", e]
        send ["check-sat"]
        send ["pop"]

        recv >>= \case
          "unsat"   → return False
          "sat"     → return True
          result    → error ("Unexpected check-sat response: " ++ show result)

      backendInterpolate (assert :| asserts) = do
        send (List ("compute-interpolant" : assert : asserts))
        recv >>= \case
          "unsat"   → recv >>= \case
                        List ("interpolants" : itps) → return (Just itps)
                        result                       → error ("Unexpected interpolation response: " ++ show result)
          "sat"     → return Nothing
          "unknown" → return Nothing
          result    → error ("Unexpected interpolation response: " ++ show result)

  return Backend {..}
