{-# LANGUAGE UnicodeSyntax #-}

module Weaver.Options where

import           Prelude hiding (lookup, putStrLn, readFile)
import           Control.Applicative (Alternative (..),)
import           Language.SMT.Backend (Backend)
import           Language.SMT.Backend.CVC4 (cvc4)
import           Language.SMT.Backend.Hybrid (hybrid)
import           Language.SMT.Backend.MathSAT (mathSAT)
import           Language.SMT.Backend.SMTInterpol (smtInterpol)
import           Language.SMT.Backend.Yices (yices)
import           Language.SMT.Backend.Z3 (z3)
import           Numeric.Natural (Natural)
import           Options.Applicative (execParser, flag, option, info, long, maybeReader, metavar, short, strArgument)
import           Text.Read (readMaybe)

data Method
  = FloydHoare
  | Partition
  | PartitionSets
  | PartitionProgress
  | PartitionProgressSets
  | TotalOrder

data DebugMode
  = Debug
  | NoDebug
  deriving Eq

data Bound
  = NoBound
  | BoundLeft Natural
  | BoundRight Natural
  | BoundMiddle Natural
  | BoundUniform Natural
  | BoundAzadeh Natural
  | BoundRoundRobin

data TestMode
  = Test
  | NoTest
  deriving Eq

data Options = Options FilePath Method (IO Backend) DebugMode TestMode Bound Natural

parseOptions ∷ IO Options
parseOptions = execParser (info optionsParser mempty)
  where optionsParser = Options
          <$> strArgument (metavar "FILENAME")
          <*> options method  "method" 'm' FloydHoare
          <*> options backend "solver" 's' (hybrid yices mathSAT)
          <*> flag NoDebug Debug (long "debug" <> short 'd')
          <*> flag NoTest Test (long "test" <> short 't')
          <*> options bound   "bound"  'b' NoBound
          <*> options readMaybe "iterations" 'i' 0

        method  "floydhoare"              = Just FloydHoare
        method  "partition"               = Just Partition
        method  "partition-sets"          = Just PartitionSets
        method  "partition-progress"      = Just PartitionProgress
        method  "partition-progress-sets" = Just PartitionProgressSets
        method  "total-order"             = Just TotalOrder
        method  _                         = Nothing

        backend "mathsat"             = Just mathSAT
        backend "smtinterpol"         = Just smtInterpol
        backend "z3"                  = Just z3
        backend "yices-mathsat"       = Just (hybrid yices mathSAT)
        backend "z3-mathsat"          = Just (hybrid z3 mathSAT)
        backend "cvc4-mathsat"        = Just (hybrid cvc4 mathSAT)
        backend "smtinterpol-mathsat" = Just (hybrid smtInterpol mathSAT)
        backend "yices-z3"            = Just (hybrid yices z3)
        backend "mathsat-z3"          = Just (hybrid mathSAT z3)
        backend "cvc4-z3"             = Just (hybrid cvc4 z3)
        backend "smtinterpol-z3"      = Just (hybrid smtInterpol z3)
        backend "yices-smtinterpol"   = Just (hybrid yices smtInterpol)
        backend "mathsat-smtinterpol" = Just (hybrid mathSAT smtInterpol)
        backend "cvc4-smtinterpol"    = Just (hybrid cvc4 smtInterpol)
        backend "z3-smtinterpol"      = Just (hybrid z3 smtInterpol)
        backend _                     = Nothing

        bound xs       | Just n ← readMaybe xs = Just (BoundLeft    n)
        bound ('r':xs) | Just n ← readMaybe xs = Just (BoundRight   n)
        bound ('l':xs) | Just n ← readMaybe xs = Just (BoundLeft    n)
        bound ('m':xs) | Just n ← readMaybe xs = Just (BoundMiddle  n)
        bound ('u':xs) | Just n ← readMaybe xs = Just (BoundUniform n)
        bound ('a':xs) | Just n ← readMaybe xs = Just (BoundAzadeh  n)
        bound "rr" = Just BoundRoundRobin
        bound _ = Nothing

        options f l s d = option (maybeReader f) (long l <> short s) <|> pure d
