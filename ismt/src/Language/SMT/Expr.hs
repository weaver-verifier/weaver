{-# LANGUAGE
    BlockArguments,
    DataKinds,
    GADTs,
    OverloadedLists,
    OverloadedStrings,
    RankNTypes,
    TypeFamilies,
    TypeOperators,
    UnicodeSyntax
  #-}

module Language.SMT.Expr (
  Expr, emap, ebind,
  etraverse_, etraverse,
  Args, var, true, false, nat,
  add, sub, mul, div,
  lt, gt, le, ge, eq, ne,
  not, and, or, imp, ite,
  store, select
) where

import Prelude hiding (and, div, not, or)
import Data.Coerce (coerce)
import Data.Foldable (traverse_)
import Data.Functor.Identity (Identity (..))
import Data.Some (Some (..))
import Data.Text (Text)
import Language.SMT.Expr.Internal (Expr (..))
import Language.SMT.SExpr (SExpr (..))
import Language.SMT.Var (Array, Sorts (..), Rank (..), Var (..))
import Numeric.Natural (Natural)

emap ∷ (∀ b. v b → v b) → Expr v a → Expr v a
emap f = runIdentity . etraverse (Identity . f)

ebind ∷ Var v ⇒ (∀ b. v '( '[], b) → Expr v b) → Expr v a → Expr v a
ebind f (Expr e) = Expr (e >>= \(Some x) →
  case rank x of
    Rank SNil        _ → getExpr (f x)
    Rank (SCons _ _) _ → Variable (Some x))

etraverse_ ∷ Applicative f ⇒ (∀ b. v b → f c) → Expr v a → f ()
etraverse_ f (Expr e) = traverse_ (\(Some x) → f x) e

etraverse ∷ Applicative f ⇒ (∀ b. v b → f (v b)) → Expr v a → f (Expr v a)
etraverse f (Expr e) = Expr <$> traverse (\(Some x) → fmap Some (f x)) e

type family Args v p where
  Args v '[]     = ()
  Args v (a ': p) = (Expr v a, Args v p)

var ∷ Var v ⇒ v '(p, a) → Args v p → Expr v a
var v =
  case rank v of
    Rank SNil _ → \_ → Expr (Variable (Some v))
    Rank xs   _ → \p → Expr (List (Variable (Some v) : go xs p))
  where go ∷ Sorts p → Args v p → [SExpr (Some v)]
        go SNil        ()           = []
        go (SCons _ p) (Expr x, xs) = x : go p xs

true, false ∷ Expr v Bool
true  = Expr "true"
false = Expr "false"

nat ∷ Natural → Expr v Integer
nat x = Expr (Numeral x)

add, sub, mul ∷ [Expr v Integer] → Expr v Integer
add = variadicDefault "+" (nat 0) id
sub = variadicDefault "-" (nat 0) (unary "-")
mul = variadicDefault "*" (nat 1) id

div ∷ Expr v Integer → Expr v Integer → Expr v Integer
div = binary "/"

lt, gt, le, ge ∷ Expr v Integer → Expr v Integer → Expr v Bool
lt = binary "<"
gt = binary ">"
le = binary "<="
ge = binary ">="

eq, ne ∷ [Expr v a] → Expr v Bool
eq = variadicDefault "="        true (\_ → true)
ne = variadicDefault "distinct" true (\_ → true)

not ∷ Expr v Bool → Expr v Bool
not = unary "not"

and, or, imp ∷ [Expr v Bool] → Expr v Bool
and = variadicDefault "and" true  id
or  = variadicDefault "or"  false id
imp = variadicDefault "=>"  true  id

ite ∷ Expr v Bool → Expr v a → Expr v a → Expr v a
ite (Expr b) (Expr e₁) (Expr e₂) = Expr ["ite", b, e₁, e₂]

variadic ∷ Text → [Expr v a] → Expr v b
variadic op es = Expr (List (Symbol op : coerce es))

variadicDefault ∷ Text → Expr v b → (Expr v a → Expr v b) → [Expr v a] → Expr v b
variadicDefault _ e _ []  = e
variadicDefault _ _ f [e] = f e
variadicDefault s _ _ es  = variadic s es

binary ∷ Text → Expr v a → Expr v a → Expr v b
binary op x y = variadic op [x, y]

unary ∷ Text → Expr v a → Expr v a
unary op x = variadic op [x]

store ∷ Expr v (Array a b) → Expr v a → Expr v b → Expr v (Array a b)
store (Expr e₁) (Expr e₂) (Expr e₃) = Expr ["store", e₁, e₂, e₃]

select ∷ Expr v (Array a b) → Expr v a → Expr v b
select (Expr e₁) (Expr e₂) = Expr ["select", e₁, e₂]
