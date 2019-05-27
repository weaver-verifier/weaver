{-# LANGUAGE
    BlockArguments,
    DataKinds,
    GADTs,
    KindSignatures,
    OverloadedLists,
    OverloadedStrings,
    RecordWildCards,
    UnicodeSyntax
  #-}

module Language.SMT.Solver (
  Solver, newSolver,
  isSatisfiable, isValid, interpolate
) where

import Prelude hiding (lookup)
import Control.Monad (join)
import Control.Monad.IO.Class (MonadIO (..))
import Data.Bimap (Bimap, empty, insert, lookup, lookupR)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import Data.List.NonEmpty (NonEmpty)
import Data.Some (Some (..))
import Data.Text (Text, pack)
import Data.Void (Void, absurd)
import Language.SMT.Backend (Backend (..))
import Language.SMT.Expr.Internal (Expr (..))
import Language.SMT.SExpr (SExpr (..), SExpressible (..))
import Language.SMT.Var (Var (..), Rank (..))

data Solver (v ∷ ([*], *) → *) = Solver {
  backend  ∷ Backend,
  declared ∷ IORef (Bimap (Some v) Text),
  counter  ∷ IORef Integer
}

newSolver ∷ MonadIO m ⇒ IO Backend → m (Solver v)
newSolver backendProc = liftIO do
  backend  ← backendProc
  declared ← newIORef empty
  counter  ← newIORef 0
  return Solver {..}

isSatisfiable ∷ (Var v, MonadIO m) ⇒ Solver v → Expr v a → m Bool
isSatisfiable solver@Solver {..} (Expr expr) = liftIO do
  expr' ← traverse (reference solver) expr
  backendSatisfiable backend (join expr')

isValid ∷ (Var v, MonadIO m) ⇒ Solver v → Expr v a → m Bool
isValid solver (Expr expr) = not <$> isSatisfiable solver (Expr ["not", expr])

interpolate ∷ (Var v, MonadIO m) ⇒ Solver v → NonEmpty (Expr v a) → m (Maybe [Expr v a])
interpolate solver@Solver {..} exprs = liftIO do
  exprs'    ← mapM (fmap join . traverse (reference solver) . getExpr) exprs
  result    ← backendInterpolate backend exprs'
  declared₀ ← readIORef declared
  let reparse (Symbol k)   = maybe (Symbol k) Variable (lookupR k declared₀)
      reparse (Numeral x)  = Numeral x
      reparse (Decimal x)  = Decimal x
      reparse (String x)   = String x
      reparse (Keyword x)  = Keyword x
      reparse (List xs)    = List (map reparse xs)
      reparse (Variable x) = absurd x
  return (fmap (Expr . reparse) <$> result)

reference ∷ Var v ⇒ Solver v → Some v → IO (SExpr Void)
reference Solver {..} var'@(This var) = do
  declared₀ ← readIORef declared
  case lookup var' declared₀ of
    Just name → return (Symbol name)
    Nothing   → do
      index ← readIORef counter
      writeIORef counter (index + 1)
      let name = pack ('x' : show index)
      writeIORef declared (insert var' name declared₀)
      case rank var of
        Rank args ret → do
          backendDeclare backend (Symbol name) (toSExpr args) (toSExpr ret)
          return (Symbol name)
