{-# LANGUAGE
    BlockArguments,
    ConstraintKinds,
    FlexibleContexts,
    GADTs,
    LambdaCase,
    OverloadedLists,
    OverloadedStrings,
    PatternSynonyms,
    UnicodeSyntax,
    ViewPatterns
  #-}

module Weaver.Program (
  Tag, compareIndep, conflicts,
  Program (..), compile
) where

import Prelude hiding (and, concat, div, lookup, not, or)
import Control.Monad (when)
import Control.Monad.Except (MonadError (..))
import Control.Monad.IO.Class (MonadIO (..))
import Control.Monad.Reader (MonadReader (..), runReaderT)
import Control.Monad.State (MonadState (..), runStateT)
import Control.Monad.Writer (MonadWriter (..), runWriterT)
import Data.Automata.Regex (Regex (..))
import Data.Bifunctor (first)
import Data.Finite.Container (Container, Index, reify)
import Data.Functor.Product (Product (..))
import Data.GADT.Compare (GEq (..))
import Data.Map (Map, empty, insert, lookup, member)
import Data.Some (Some (..))
import Data.Text (Text, concat)
import Data.Type.Equality ((:~:) (..))
import Data.Void (Void)
import Language.SMT.Expr
import Language.SMT.SExpr (SExpr (..), SExpressible (..), pretty)
import Language.SMT.Var (Var (..), Sort (..), Sorts (..), Rank (..))
import Weaver.Stmt (V, mkV, Stmt (..))

data Tag = DepLeft | DepRight | IndepLeft | IndepRight
  deriving (Eq, Ord, Show)

compareIndep ∷ [Tag] → [Tag] → Ordering
compareIndep (DepLeft:xs) ys = compareIndep xs ys
compareIndep (DepRight:xs) ys = compareIndep xs ys
compareIndep xs (DepLeft:ys) = compareIndep xs ys
compareIndep xs (DepRight:ys) = compareIndep xs ys
compareIndep [] [] = EQ
compareIndep [] _  = LT
compareIndep _  [] = GT
compareIndep (IndepLeft:xs) (IndepLeft:ys) = compareIndep xs ys
compareIndep (IndepLeft:_) (IndepRight:_) = LT
compareIndep (IndepRight:_) (IndepLeft:_) = GT
compareIndep (IndepRight:xs) (IndepRight:ys) = compareIndep xs ys

conflicts ∷ [Tag] → [Tag] → Bool
conflicts (IndepLeft:_)   (IndepRight:_)  = False
conflicts (IndepRight:_)  (IndepLeft:_)   = False
conflicts (IndepLeft:xs)  (IndepLeft:ys)  = conflicts xs ys
conflicts (IndepRight:xs) (IndepRight:ys) = conflicts xs ys
conflicts (DepLeft:_)     (DepRight:_)    = True
conflicts (DepRight:_)    (DepLeft:_)     = True
conflicts (DepLeft:xs)    (DepLeft:ys)    = conflicts xs ys
conflicts (DepRight:xs)   (DepRight:ys)   = conflicts xs ys
conflicts _               _               = True

extend ∷ Functor f ⇒ a → f ([a], c) → f ([a], c)
extend x = fmap (first (x:))

tag ∷ Regex a → Regex ([Tag], a)
tag Emp = Emp
tag Nil = Nil
tag (Sym x) = Sym ([], x)
tag (Alt x y) = Alt (extend DepLeft (tag x)) (extend DepRight (tag y))
tag (Cat x y) = Cat (extend DepLeft (tag x)) (extend DepRight (tag y))
tag (Par x y) = Par (extend IndepLeft (tag x)) (extend IndepRight (tag y))
tag (Rep x) = Rep (tag x)

data Program = ∀ c. Container c ([Tag], Stmt) ⇒ Program [Expr V Bool] (Regex (Index c))

compile ∷ (MonadIO m, MonadError Text m) ⇒ [SExpr Void] → m Program
compile ss = do
  ((ss', env), stmts) ← runWriterT (runStateT (compileEnv ss) empty)
  body ← runReaderT (compileBody ss') env
  pure (reify (tag body) (Program stmts))

type Env = Map Text (Some V)

compileEnv ∷ (MonadIO m, MonadError Text m, MonadState Env m, MonadWriter [Expr V Bool] m) ⇒ [SExpr Void] → m [SExpr Void]
compileEnv [] = return []
compileEnv ss'@(s:ss) = do
  ok ← compileDecl s
  if ok
    then compileEnv ss
    else return ss'

unsnoc ∷ [a] → Maybe ([a], a)
unsnoc []     = Nothing
unsnoc [x]    = Just ([], x)
unsnoc (x:xs) = fmap (first (x:)) (unsnoc xs)

pattern (:>) ∷ [a] → a → [a]
pattern xs :> x ← (unsnoc → Just (xs, x))

toSymbol ∷ SExpr a → Maybe Text
toSymbol (Symbol x) = Just x
toSymbol _          = Nothing

pattern Symbols ∷ [Text] → [SExpr a]
pattern Symbols xs ← (traverse toSymbol → Just xs)

toSort ∷ Eq a ⇒ SExpr a → Maybe (Some Sort)
toSort "Int" = Just (This Integer)
toSort "Bool" = Just (This Bool)
toSort (List ["Array", a, b]) = do
  This a' ← toSort a
  This b' ← toSort b
  return (This (Array a' b'))
toSort _ = Nothing

toSorts ∷ Eq a ⇒ [SExpr a] → Maybe (Some Sorts)
toSorts [] = Just (This SNil)
toSorts (x:xs) = do
  This x'  ← toSort x
  This xs' ← toSorts xs
  return (This (SCons x' xs'))

pattern Sort ∷ Eq b ⇒ Sort a → SExpr b
pattern Sort a ← (toSort → Just (This a))

pattern Sorts ∷ Eq b ⇒ Sorts a → [SExpr b]
pattern Sorts a ← (toSorts → Just (This a))

compileDecl ∷ (MonadIO m, MonadError Text m, MonadState Env m, MonadWriter [Expr V Bool] m) ⇒ SExpr Void → m Bool
compileDecl (List ("var" : Symbols xs :> Sort a)) = do
  mapM_ (addDecl (Rank SNil a)) xs
  return True
compileDecl (List ("var" : Symbols xs :> List (Sorts ts) :> Sort a)) = do
  mapM_ (addDecl (Rank ts a)) xs
  return True
compileDecl (List ("use" : xs)) = do
  env ← get
  xs' ← traverse (\x → runReaderT (compileExpr Bool x) env) xs
  tell xs'
  return True
compileDecl _ = return False

addDecl ∷ (MonadIO m, MonadError Text m, MonadState Env m, MonadWriter [Expr V Bool] m) ⇒ Rank a → Text → m ()
addDecl s x = do
  env ← get
  when (member x env) do
    report ["Variable `", x, "' is declared multiple times"]
  put (insert x (This (mkV x s)) env)

compileBody ∷ (MonadReader Env m, MonadError Text m) ⇒ [SExpr Void] → m (Regex Stmt)
compileBody = fmap (foldr Cat Nil) . traverse compileStmts

compileStmts ∷ (MonadReader Env m, MonadError Text m) ⇒ SExpr Void → m (Regex Stmt)
compileStmts (List ("cond":ss)) = foldr Alt Emp <$> traverse compileStmts ss
compileStmts (List ("seq":ss))  = foldr Cat Nil <$> traverse compileStmts ss
compileStmts (List ("par":ss))  = foldr Par Nil <$> traverse compileStmts ss
compileStmts (List ("loop":ss))
  | ("par":_) ← ss = report ["The first statement of a loop cannot be a `par' statement"]
  | otherwise      = Rep <$> compileStmts (List ("seq":ss))
compileStmts (List ("while":e:ss)) = compileStmts
  [ "seq"
  , List ("loop":["assume", e]:ss)
  , ["assume", ["not", e]]
  ]
compileStmts (List ["if", e, s₁, s₂]) = compileStmts
  [ "cond"
  , ["seq", ["assume", e], s₁]
  , ["seq", ["assume", ["not", e]], s₂]
  ]
compileStmts (List ["if", e, s]) = compileStmts
  [ "cond"
  , ["seq", ["assume", e], s]
  , ["assume", ["not", e]]
  ]
compileStmts s = Sym <$> compileStmt s

compileStmt ∷ (MonadReader Env m, MonadError Text m) ⇒ SExpr Void → m Stmt
compileStmt (List ["assume", e]) = Assume <$> compileExpr Bool e
compileStmt (List ["set!", Symbol x, e]) = do
  This x' ← lookupVar x
  case rank x' of
    Rank (SCons _ _) _ → report ["Cannot set! function `", x, "'"]
    Rank SNil        t → do
      e' ← compileExpr t e
      return (Assign x' e')
compileStmt (List ["havoc!", Symbol x]) = do
  This x' ← lookupVar x
  case rank x' of
    Rank SNil _ → return (Havoc x')
    _           → report ["Cannot havoc! function `", x, "'"]
compileStmt (List ("atomic" : ss)) = Atomic <$> traverse compileStmt ss
compileStmt (List ["store!", e₁, e₂, e₃]) = compileStmt ["set!", e₁, ["store", e₁, e₂, e₃]]
compileStmt s = report ["Unrecognized statement `", pretty s, "'"]

compileExpr ∷ (MonadReader Env m, MonadError Text m) ⇒ Sort a → SExpr Void → m (Expr V a)
compileExpr t e = do
  This (Pair e' t') ← inferExpr e
  case geq t t' of
    Just Refl → return e'
    Nothing   → report ["Expected type `", pretty (toSExpr t), "' but got `", pretty (toSExpr t'), "' for the expression `", pretty e, "'"]

compileExprs ∷ (MonadReader Env m, MonadError Text m) ⇒ Sorts a → [SExpr Void] → m (Args V a)
compileExprs SNil [] = return ()
compileExprs SNil _ = report ["Function has too many arguments"]
compileExprs (SCons a p) (x:xs) = (,) <$> compileExpr a x <*> compileExprs p xs
compileExprs (SCons _ _) [] = report ["Function does not have enough arguments"]

inferExpr ∷ (MonadReader Env m, MonadError Text m) ⇒ SExpr Void → m (Some (Product (Expr V) Sort))
inferExpr (Numeral n)         = return (This (Pair (nat n) Integer))
inferExpr (Symbol "true")     = return (This (Pair true Bool))
inferExpr (Symbol "false")    = return (This (Pair false Bool))
inferExpr (List ["not", x])   = unaryOp Bool Bool not x
inferExpr (List ("and" : xs)) = variadicOp Bool Bool and xs
inferExpr (List ("or"  : xs)) = variadicOp Bool Bool or xs
inferExpr (List ("=>"  : xs)) = variadicOp Bool Bool imp xs
inferExpr (List ("+"   : xs)) = variadicOp Integer Integer add xs
inferExpr (List ("-"   : xs)) = variadicOp Integer Integer sub xs
inferExpr (List ("*"   : xs)) = variadicOp Integer Integer mul xs
inferExpr (List ["/",  x, y]) = binaryOp Integer Integer div x y
inferExpr (List ["<",  x, y]) = binaryOp Integer Bool lt x y
inferExpr (List [">",  x, y]) = binaryOp Integer Bool gt x y
inferExpr (List ["<=", x, y]) = binaryOp Integer Bool le x y
inferExpr (List [">=", x, y]) = binaryOp Integer Bool ge x y
inferExpr (List ("=" : x : xs)) = do
  This (Pair e t) ← inferExpr x
  variadicOp t Bool (eq . (e:)) xs
inferExpr (List ("/=" : x : xs)) = do
  This (Pair e t) ← inferExpr x
  variadicOp t Bool (ne . (e:)) xs
inferExpr (List ["if", x, y, z]) = do
  e₁               ← compileExpr Bool x
  This (Pair e₂ t) ← inferExpr y
  e₃               ← compileExpr t z
  return (This (Pair (ite e₁ e₂ e₃) t))
inferExpr (List ["store", x, y, z]) = do
  This (Pair ey ty) ← inferExpr y
  This (Pair ez tz) ← inferExpr z
  ex ← compileExpr (Array ty tz) x
  return (This (Pair (store ex ey ez) (Array ty tz)))
inferExpr (List ["select", x, y]) = do
  This (Pair ex tx) ← inferExpr x
  case tx of
    Array a b → do
      ey ← compileExpr a y
      return (This (Pair (select ex ey) b))
    _         → report ["Expected array type but got `", pretty (toSExpr tx), "' for the expression `", pretty x, "'"]
inferExpr (List (Symbol x : xs)) = do
  This x' ← lookupVar x
  case rank x' of
    Rank p r → do
      xs' ← compileExprs p xs
      return (This (Pair (var x' xs') r))
inferExpr (Symbol x) = do
  This x' ← lookupVar x
  case rank x' of
    Rank SNil t → return (This (Pair (var x' ()) t))
    _           → report ["Function `", x, "' is missing arguments"]
inferExpr e = report ["Unknown expression `", pretty e, "'"]

lookupVar ∷ (MonadReader Env m, MonadError Text m) ⇒ Text → m (Some V)
lookupVar x = do
  env ← ask
  case lookup x env of
    Just x' → return x'
    Nothing → report ["Variable `", x, "' not in scope"]

variadicOp ∷ (MonadReader Env m, MonadError Text m)
           ⇒ Sort a → Sort b → ([Expr V a] → Expr V b)
           → [SExpr Void] → m (Some (Product (Expr V) Sort))
variadicOp t₁ t₂ f xs = do
  xs' ← traverse (compileExpr t₁) xs
  return (This (Pair (f xs') t₂))

binaryOp ∷ (MonadReader Env m, MonadError Text m)
         ⇒ Sort a → Sort b → (Expr V a → Expr V a → Expr V b)
         → SExpr Void → SExpr Void → m (Some (Product (Expr V) Sort))
binaryOp t₁ t₂ f x y = do
  x' ← compileExpr t₁ x
  y' ← compileExpr t₁ y
  return (This (Pair (f x' y') t₂))

unaryOp ∷ (MonadReader Env m, MonadError Text m)
        ⇒ Sort a → Sort b → (Expr V a → Expr V b)
        → SExpr Void → m (Some (Product (Expr V) Sort))
unaryOp t₁ t₂ f x = do
  x' ← compileExpr t₁ x
  return (This (Pair (f x') t₂))

report ∷ MonadError Text m ⇒ [Text] → m a
report = throwError . concat
