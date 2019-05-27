{-# LANGUAGE
    LambdaCase,
    OverloadedLists,
    OverloadedStrings,
    RecordWildCards,
    UnicodeSyntax
  #-}

module Language.SMT.Backend.SMTInterpol where

import Control.Monad.IO.Class (MonadIO (..))
import Data.List.NonEmpty (toList)
import Data.IORef (newIORef, readIORef, writeIORef)
import Data.Semigroup ((<>))
import Data.Text (pack)
import Data.Traversable (for)
import Numeric.Natural (Natural)
import Language.SMT.Backend
import Language.SMT.SExpr

smtInterpol ∷ MonadIO m ⇒ m Backend
smtInterpol = liftIO $ do
  (send, recv) ← openPipe "java"
    [ "-Xss20000k"
    , "-Xmx1500m"
    , "-noverify"
    , "de.uni_freiburg.informatik.ultimate.smtinterpol.Main"
    ]
    Nothing

  let write e = send e >> recv

      success e = do
        result ← write e
        case result of
          "success" → return ()
          _         → error ("Unexpected solver output: " ++ show result)

  success ["set-option", ":verbosity", 2]
  success ["set-option", ":produce-interpolants", "true"]
  success ["set-logic", "QF_UFLIA"]

  let backendDeclare x ps r = success ["declare-fun", x, ps, r]

      backendSatisfiable e = do
        success ["push"]
        success ["assert", e]
        result ← write ["check-sat"]
        success ["pop"]
        case result of
          "unsat"   → return False
          "sat"     → return True
          _         → error ("Unexpected check-sat response: " ++ show result)

      backendInterpolate es = do
        success ["push"]

        count  ← newIORef (0 ∷ Natural)

        groups ← for es $ \e → do
          i ← readIORef count
          writeIORef count (i + 1)
          let group = Symbol ("g" <> pack (show i))
          success ["assert", ["!", e, ":named", group]]
          return group

        result ← write ["check-sat"] >>= \case
          "unsat"   → write (List ("get-interpolants" : toList groups)) >>= \case
                        List itps → return (Just itps)
                        result    → error ("Unexpected interpolation response: " ++ show result)
          "sat"     → return Nothing
          "unknown" → return Nothing
          result    → error ("Unexpected check-sat response: " ++ show result)

        success ["pop"]

        return result

  return Backend {..}
