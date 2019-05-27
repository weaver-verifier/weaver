{-# LANGUAGE LambdaCase, OverloadedStrings, UnicodeSyntax #-}

module Language.SMT.Backend where

import Control.Exception (Exception, throw)
import Data.IORef (newIORef, readIORef, writeIORef)
import Data.List.NonEmpty (NonEmpty)
import Data.Text (Text, unpack)
import Data.Text.IO (hGetChunk, hPutStrLn)
import Data.Void (Void)
import System.IO (hFlush)
import System.Process (CreateProcess (..), createProcess, StdStream (..), proc)
import Language.SMT.SExpr (SExpr (..), parse, pretty)

data Backend = Backend {
  backendDeclare     ∷ SExpr Void → SExpr Void → SExpr Void → IO (),
  backendSatisfiable ∷ SExpr Void → IO Bool,
  backendInterpolate ∷ NonEmpty (SExpr Void) → IO (Maybe [SExpr Void])
}

newtype BackendException = BackendException Text
  deriving Show

instance Exception BackendException

newtype ParseException = ParseException Text
  deriving Show

instance Exception ParseException

openPipe ∷ FilePath → [String] → Maybe FilePath → IO (SExpr Void → IO (), IO (SExpr Void))
openPipe path args script = do
  let cp = (proc path args) { std_in = CreatePipe, std_out = CreatePipe }
  (Just stdin, Just stdout, _, _) ← createProcess cp

  saved ← newIORef mempty

  let send expr = do
        case script of
          Just scriptPath → appendFile scriptPath (unpack (pretty expr) <> "\n")
          Nothing         → return ()
        hPutStrLn stdin (pretty expr)
        hFlush stdin

      recv = do
        initial ← readIORef saved
        parse (hGetChunk stdout) initial >>= \case
          Right (List ["error", String msg], _) → throw (BackendException msg)
          Right (expr, rest) → expr <$ writeIORef saved rest
          Left msg           → throw (ParseException msg)

  return (send, recv)
