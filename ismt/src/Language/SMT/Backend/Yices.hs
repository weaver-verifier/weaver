{-# LANGUAGE
    LambdaCase,
    OverloadedLists,
    OverloadedStrings,
    RecordWildCards,
    UnicodeSyntax
  #-}

module Language.SMT.Backend.Yices where

import Language.SMT.Backend

yices ∷ Maybe FilePath → IO Backend
yices script = do
  (send, recv) ← openPipe "yices-smt2"
    ["--incremental"]
    script
  send ["set-logic", "QF_AUFLIA"]

  let backendDeclare x ps r = send ["declare-fun", x, ps, r]

      backendSatisfiable e = do
        send ["push", 1]
        send ["assert", e]
        send ["check-sat"]
        send ["pop", 1]

        recv >>= \case
          "unsat"   → return False
          "sat"     → return True
          result    → error ("Unexpected check-sat response: " ++ show result)

      backendInterpolate = error "yices: unsupported"

  return Backend {..}
