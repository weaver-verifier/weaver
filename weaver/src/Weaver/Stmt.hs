{-# LANGUAGE
    BlockArguments,
    DataKinds,
    GADTs,
    MultiParamTypeClasses,
    OverloadedLists,
    OverloadedStrings,
    UnicodeSyntax
  #-}

module Weaver.Stmt (V, mkV, Stmt (..), prove, isTriple, isSwappable, isIndep) where

import qualified Prelude as P
import Prelude hiding (and, not)
import Control.Monad.IO.Class (MonadIO (..))
import Control.Monad.State (State, evalState, get, modify', put, runState)
import Data.Dependent.Sum (EqTag (..))
import Data.Dependent.Map (DMap, empty, findWithDefault, foldrWithKey, insert)
import Data.GADT.Compare (GEq (..), GCompare (..), GOrdering (..), gcompare, geq)
import Data.List.NonEmpty (NonEmpty)
import Data.Maybe (isJust)
import Data.Text (Text)
import Data.Type.Equality ((:~:) (..))
import Language.SMT.Expr (Expr, and, ebind, eq, emap, not, var, imp, true)
import Language.SMT.SExpr (SExpr (..), SExpressible (..))
import Language.SMT.Solver (Solver, interpolate, isSatisfiable, isValid)
import Language.SMT.Var (Var (..), Sorts (..), Rank (..))
import Numeric.Natural (Natural)

data V a = V Text Natural (Rank a)

instance SExpressible (V a) where
  toSExpr (V x _ _) = Symbol x

mkV ∷ Text → Rank a → V a
mkV x s = V x 0 s

prime ∷ V a → V a
prime (V x i s) = V x (i + 1) s

unprime ∷ V a → V a
unprime (V x _ s) = V x 0 s

instance GEq V where
  geq (V x₁ i₁ s₁) (V x₂ i₂ s₂)
    | (x₁, i₁) == (x₂, i₂) = geq s₁ s₂
    | otherwise            = Nothing

instance GCompare V where
  gcompare (V x₁ i₁ s₁) (V x₂ i₂ s₂) =
    case compare (x₁, i₁) (x₂, i₂) of
      LT → GLT
      GT → GGT
      EQ → gcompare s₁ s₂

instance Var V where
  rank (V _ _ s) = s

newtype U a = U { toV ∷ V '( '[], a) }

instance EqTag U U where
  eqTagged (U _) (U _) x y = isJust (geq x y)

instance GEq U where
  geq (U x₁) (U x₂) = do
    Refl ← geq x₁ x₂
    return Refl

instance GCompare U where
  gcompare (U x₁) (U x₂) =
    case gcompare x₁ x₂ of
      GLT → GLT
      GEQ → GEQ
      GGT → GGT

data Stmt
  = Assume (Expr V Bool)
  | ∀ a. Assign (V '( '[], a)) (Expr V a)
  | Atomic [Stmt]

instance Eq Stmt where
  Assume φ == Assume ψ = φ == ψ
  Assign x₁ expr₁ == Assign x₂ expr₂ =
    case geq x₁ x₂ of
      Just Refl → expr₁ == expr₂
      Nothing   → False
  Atomic stmts₁ == Atomic stmts₂ = stmts₁ == stmts₂
  _ == _ = False

instance Ord Stmt where
  compare (Assume φ) (Assume ψ) = compare φ ψ
  compare (Assume _) _ = LT
  compare _ (Assume _) = GT
  compare (Assign x₁ expr₁) (Assign x₂ expr₂) =
    case gcompare x₁ x₂ of
      GLT → LT
      GGT → GT
      GEQ → compare expr₁ expr₂
  compare (Assign _ _) _ = LT
  compare _ (Assign _ _) = GT
  compare (Atomic stmts₁) (Atomic stmts₂) = compare stmts₁ stmts₂

instance SExpressible Stmt where
  toSExpr (Assume φ) = ["assume", toSExpr φ]
  toSExpr (Assign x expr) = ["set!", toSExpr x, toSExpr expr]
  toSExpr (Atomic stmts) = List ("atomic" : map toSExpr stmts)

rename ∷ DMap U U → Expr V a → Expr V a
rename m = emap \x →
  case rank x of
    Rank SNil _ → toV (findWithDefault (U x) (U x) m)
    _           → x

interpret ∷ Stmt → State (DMap U U) [Expr V Bool]
interpret (Assume φ) = (\m → [rename m φ]) <$> get
interpret (Atomic stmts) = concat <$> traverse interpret stmts
interpret (Assign x expr) = do
  m ← get
  let x'    = prime (toV (findWithDefault (U x) (U x) m))
      expr' = rename m expr
  put (insert (U x) (U x') m)
  return [eq [var x' (), expr']]

shift ∷ Traversable f ⇒ f Stmt → f (Expr V Bool)
shift stmts = and <$> evalState (traverse interpret stmts) empty

subst ∷ DMap U (Expr V) → Expr V a → Expr V a
subst m = ebind \x → findWithDefault (var x ()) (U x) m

evaluate ∷ Stmt → State (DMap U (Expr V)) [Expr V Bool]
evaluate (Assume φ) = (\m → [subst m φ]) <$> get
evaluate (Atomic stmts) = concat <$> traverse evaluate stmts
evaluate (Assign x expr) = do
  modify' \m → insert (U x) (subst m expr) m
  return []

compress ∷ Stmt → Expr V Bool
compress stmt =
  let (exprs, binds) = runState (evaluate stmt) empty
  in  and (foldrWithKey (\x e φs → eq [var (prime (toV x)) (), e] : φs) exprs binds)

prove ∷ MonadIO m ⇒ Solver V → NonEmpty Stmt → m (Maybe [Expr V Bool])
prove solver = fmap (fmap (fmap (emap unprime))) . interpolate solver . shift

isTriple ∷ MonadIO m ⇒ Solver V → Expr V Bool → Stmt → Expr V Bool → m Bool
isTriple solver φ stmt ψ =
  P.not <$> isSatisfiable solver (and (shift [Assume φ, stmt, Assume (not ψ)]))

isSwappable ∷ MonadIO m ⇒ Solver V → Stmt → Stmt → m Bool
isSwappable solver = isIndep solver true

isIndep ∷ MonadIO m ⇒ Solver V → Expr V Bool → Stmt → Stmt → m Bool
isIndep solver φ stmt₁ stmt₂ = do
  let expr₁ = compress (Atomic [stmt₁, stmt₂])
      expr₂ = compress (Atomic [stmt₂, stmt₁])
  isValid solver (imp [φ, expr₁, expr₂])
