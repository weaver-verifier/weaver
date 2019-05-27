{-# LANGUAGE
    DeriveTraversable,
    OverloadedLists,
    OverloadedStrings,
    TypeFamilies,
    UnicodeSyntax
  #-}

module Language.SMT.SExpr (
  SExpr (..), parse, parseAll,
  SExpressible (..), pretty, prettyPrint,
  isAlphaNum
) where

import Prelude hiding (putStrLn, takeWhile, unwords)
import Control.Applicative (many)
import Control.Monad (ap)
import Data.Attoparsec.Text hiding (parse)
import Data.Bifunctor (first)
import Data.Scientific (Scientific, FPFormat (..), formatScientific)
import Data.String (IsString (..))
import Data.Text (Text, cons, foldl', intercalate, pack, replace, unpack, unwords)
import Data.Text.IO (putStrLn)
import Data.Void (Void, absurd)
import GHC.Exts (IsList (..))
import Numeric.Natural (Natural)

data SExpr a
  = Variable a
  | Numeral Natural
  | Decimal Scientific
  | String Text
  | Symbol Text
  | Keyword Text
  | List [SExpr a]
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Applicative SExpr where
  pure = return
  (<*>) = ap

instance Monad SExpr where
  return = Variable
  Variable x  >>= f = f x
  Numeral  n  >>= _ = Numeral n
  Decimal  d  >>= _ = Decimal d
  String   s  >>= _ = String s
  Symbol   s  >>= _ = Symbol s
  Keyword  kw >>= _ = Keyword kw
  List     xs >>= f = List (map (>>= f) xs)

instance Num (SExpr a) where
  e₁ + e₂ = ["+", e₁, e₂]
  e₁ - e₂ = ["-", e₁, e₂]
  e₁ * e₂ = ["*", e₁, e₂]

  abs = error "abs: unsupported"
  signum = error "signum: unsupported"

  fromInteger = Numeral . fromInteger

instance IsList (SExpr a) where
  type Item (SExpr a) = SExpr a
  fromList = List
  toList = error "toList: unsupported"

instance IsString (SExpr a) where
  fromString (':':xs) = Keyword (fromString xs)
  fromString xs       = Symbol  (fromString xs)

isAlpha ∷ Char → Bool
isAlpha x = x `elem` ['a'..'z'] ++ ['A'..'Z']

isDigit ∷ Char → Bool
isDigit x = x `elem` (['0'..'9'] ∷ String)

isAlphaNum ∷ Char → Bool
isAlphaNum x = isAlpha x || isDigit x

isSpecial ∷ Char → Bool
isSpecial x = x `elem` ("+-/*=%?!.$_~&^<>@" ∷ String)

isSimple ∷ Char → Bool
isSimple x = isSpecial x || isAlphaNum x

isSimpleSymbol ∷ Text → Bool
isSimpleSymbol = go . unpack
  where go "" = False
        go s  = not (isDigit (head s)) && all isSimple s

isBinary ∷ Char → Bool
isBinary x = x == '0' || x == '1'

skipComments ∷ Parser ()
skipComments = () <$ skipSpace `sepBy` (char ';' *> manyTill anyChar endOfLine)

sexpr ∷ Parser (SExpr a)
sexpr = choice [dec, nat, key, str, sym, lst]
 where
  nat = Numeral <$> choice
    [ decimal
    , string "#x" *> hexadecimal
    , string "#b" *> binary
    ]
  dec = Decimal . read . unpack . fst <$> match (numeral *> char '.' *> numeral)
  sym = Symbol <$> choice [simple, quote '|']
  str = String . intercalate "\"" <$> many1 (quote '"')
  key = Keyword <$> (char ':' *> simple)
  lst = List <$> bracket '(' ')' (skipComments *> sexpr `sepBy` skipComments <* skipComments)

  binary = foldl' step 0 <$> takeWhile1 isBinary
   where
    step a '0' = a * 2
    step a '1' = a * 2 + 1
    step _ _   = error "impossible"

  simple = cons
    <$> satisfy (\x → isSpecial x || isAlpha x)
    <*> takeWhile isSimple

  numeral       = takeWhile1 isDigit
  bracket x y p = char x *> p <* char y
  quote x       = bracket x x (takeTill (== x))

parse ∷ Monad m ⇒ m Text → Text → m (Either Text (SExpr a, Text))
parse next = fmap go . parseWith next (skipSpace *> sexpr)
  where go (Done rest expr)  = Right (expr, rest)
        go (Fail _ []   err) = Left (pack err)
        go (Fail _ ctxs err) = Left (intercalate " > " (map pack ctxs) <> ": " <> pack err)
        go _                 = error "parse: impossible"

parseAll ∷ Text → Either Text [SExpr a]
parseAll =
  first pack .
  parseOnly (skipComments *> many (sexpr <* skipComments) <* endOfInput)

class SExpressible a where
  toSExpr ∷ a → SExpr Void

instance SExpressible Void where
  toSExpr = absurd

instance SExpressible a ⇒ SExpressible (SExpr a) where
  toSExpr x = x >>= toSExpr

pretty ∷ SExpr Void → Text
pretty (Variable x) = absurd x
pretty (Numeral n)  = pack (show n)
pretty (Decimal d)  = pack (formatScientific Fixed Nothing d)
pretty (String s)   = "\"" <> replace "\"" "\"\"" s <> "\""
pretty (Symbol s)   = if isSimpleSymbol s then s else "|" <> s <> "|"
pretty (Keyword s)  = ":" <> s
pretty (List xs)    = "(" <> unwords (map pretty xs) <> ")"

prettyPrint ∷ SExpressible a ⇒ a → IO ()
prettyPrint = putStrLn . pretty . toSExpr
