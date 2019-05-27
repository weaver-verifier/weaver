{-# LANGUAGE
    LambdaCase,
    OverloadedLists,
    OverloadedStrings,
    RecordWildCards,
    UnicodeSyntax
  #-}

module Language.SMT.Backend.CVC4 where

import Language.SMT.Backend

cvc4 ∷ IO Backend
cvc4 = do
  (send, recv) ← openPipe "cvc4"
    [ "--lang", "smt2.6.1"
    , "--incremental"
    ]
    Nothing
  send ["set-logic", "QF_AUFLIA"]

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

      backendInterpolate = error "cvc4: unsupported"

  return Backend {..}
