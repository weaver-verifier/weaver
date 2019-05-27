{-# LANGUAGE
    BlockArguments,
    LambdaCase,
    OverloadedLists,
    OverloadedStrings,
    RecordWildCards,
    UnicodeSyntax
  #-}

module Language.SMT.Backend.MathSAT where

import Prelude hiding (tail)
import Control.Exception (catch)
import Data.IORef (modifyIORef', newIORef, readIORef, writeIORef)
import Data.List.NonEmpty (tail, inits)
import Data.Traversable (for)
import Data.Text (pack)
import Language.SMT.Backend
import Language.SMT.SExpr

mathSAT ∷ IO Backend
mathSAT = do
  (send₁, recv₁) ← openPipe "mathsat" [] Nothing
  pipe₂ ← openPipe "mathsat" [] Nothing >>= newIORef
  let send₂ x = do
        (f, _) ← readIORef pipe₂
        f x
      recv₂ = do
        (_, f) ← readIORef pipe₂
        f

  send₁ ["set-logic", "QF_AXLIA"]
  send₂ ["set-logic", "QF_AXLIA"]
  send₂ ["set-option", ":produce-interpolants", "true"]

  decls ← newIORef []

  let backendDeclare x ps r = do
        let decl = ["declare-fun", x, ps, r]
        send₁ decl
        send₂ decl
        modifyIORef' decls (decl:)

      backendSatisfiable e = do
        send₁ ["push", 1]
        send₁ ["assert", e]
        send₁ ["check-sat"]
        send₁ ["pop", 1]

        recv₁ >>= \case
          "unsat"   → return False
          "sat"     → return True
          result    → error ("Unexpected check-sat response: " ++ show result)

      backendInterpolate asserts =
        backendInterpolate' asserts
          `catch` (\(BackendException _) → send₂ ["exit"] >> restart asserts)
          `catch` (\(ParseException   _) →                   restart asserts)

      restart asserts = do
        openPipe "mathsat" [] Nothing >>= writeIORef pipe₂
        send₂ ["set-logic", "QF_AXLIA"]
        send₂ ["set-option", ":produce-interpolants", "true"]
        decls₀ ← readIORef decls
        mapM_ send₂ decls₀
        backendInterpolate' asserts

      strip (List ["to_real", x]) = x
      strip (List xs) = List (map strip xs)
      strip x = x

      backendInterpolate' asserts = do
        send₂ ["push", 1]

        count ← newIORef (0 ∷ Int)

        groups ← for asserts \assert → do
          index ← readIORef count
          writeIORef count (index + 1)
          let group = Symbol ("g" <> pack (show index))
          send₂ ["assert", ["!", assert, ":interpolation-group", group]]
          return group

        send₂ ["check-sat"]

        result ← recv₂ >>= \case
          "unsat"   → Just <$> for (tail (inits groups)) \subset → do
                                 send₂ ["get-interpolant", List subset]
                                 strip <$> recv₂
          "sat"     → return Nothing
          "unknown" → return Nothing
          result    → error ("Unexpected check-sat response: " ++ show result)

        send₂ ["pop", 1]

        return result

  return Backend {..}
