{-# LANGUAGE
    RankNTypes,
    UnicodeSyntax
  #-}

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
import           Options.Applicative (execParser, flag, option, info, long, maybeReader, metavar, short, strArgument, str)
import           Text.Read (readMaybe)
import           Weaver.Algorithm (Algorithm (..))
import qualified Weaver.Algorithm.LexNF as LexNF
import qualified Weaver.Algorithm.LexNFContext as LexNFContext
import qualified Weaver.Algorithm.Normal as Normal
import qualified Weaver.Algorithm.NormalTrace as NormalTrace
import qualified Weaver.Algorithm.Partition as Partition
import qualified Weaver.Algorithm.PartitionProgress as PartitionProgress
import qualified Weaver.Algorithm.PartitionProgressTrace as PartitionProgressTrace
import qualified Weaver.Algorithm.PartitionProgressContext as PartitionProgressContext
import qualified Weaver.Algorithm.TotalOpt as TotalOpt
import qualified Weaver.Algorithm.TotalProgressOpt as TotalProgressOpt
import qualified Weaver.Algorithm.TotalProgressContext as TotalProgressContext
import qualified Weaver.Algorithm.TotalProgressContextOpt as TotalProgressContextOpt
import           Weaver.Bound (Bound (..))
import           Weaver.Config (Config (..))

data Options = Options
  FilePath
  Algorithm
  (Maybe FilePath → IO Backend)
  (Maybe FilePath)
  Config
  Bound
  Natural

parseOptions ∷ IO Options
parseOptions = execParser (info optionsParser mempty)
  where optionsParser = Options
          <$> strArgument (metavar "FILENAME")
          <*> options method  "method" 'm' Normal.algorithm
          <*> options backend "solver" 's' (hybrid yices mathSAT)
          <*> (Just <$> option str (long "script") <|> pure Nothing)
          <*> (Config <$> flag False True (long "debug" <> short 'd')
                      <*> flag False True (long "semi")
                      <*> flag False True (long "minimize"))
          <*> options bound   "bound"  'b' NoBound
          <*> options readMaybe "iterations" 'i' 0

        method  "normal"                     = Just Normal.algorithm
        method  "normal-trace"               = Just NormalTrace.algorithm
        method  "partition"                  = Just Partition.algorithm
        method  "lex-nf"                     = Just LexNF.algorithm
        method  "lex-nf-context"             = Just LexNFContext.algorithm
        -- method  "partition-sets"             = Just PartitionSets
        method  "partition-progress"         = Just PartitionProgress.algorithm
        method  "partition-progress-trace"   = Just PartitionProgressTrace.algorithm
        method  "partition-progress-context" = Just PartitionProgressContext.algorithm
        method  "total-opt"                  = Just TotalOpt.algorithm
        method  "total-progress-opt"         = Just TotalProgressOpt.algorithm
        method  "total-progress-context"     = Just TotalProgressContext.algorithm
        method  "total-progress-context-opt" = Just TotalProgressContextOpt.algorithm
        -- method  "partition-progress-sets"    = Just PartitionProgressSets
        method  _                            = Nothing

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
