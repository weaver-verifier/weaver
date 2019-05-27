{-# LANGUAGE
    BlockArguments,
    ExistentialQuantification,
    QuantifiedConstraints,
    RecursiveDo,
    ScopedTypeVariables,
    TypeApplications,
    UndecidableInstances,
    UnicodeSyntax
  #-}

module Data.Automata.GraphSpec where

import Data.Automata.Graph
import Data.Automata.Util ()
import Data.Finite (Finite)
import Data.Proxy (Proxy (..))
import Data.Vector.Sized (Vector, index)
import GHC.TypeLits (KnownNat, SomeNat (..), someNatVal)
import Test.Hspec (Spec)
import Test.LeanCheck (Listable (..), cons2, concatMapT)
import Test.LeanCheck.Utils.Types (Natural (..))

data G e = ∀ n. KnownNat n ⇒ G (Vector n (e (Finite n))) (Finite n) (Graph e)

instance (∀ n. KnownNat n ⇒ Show (e (Finite n))) ⇒ Show (G e) where
  show (G xs x _) = "Unfold (" ++ show xs ++ "!!) (" ++ show x ++ ")"

instance (∀ n. KnownNat n ⇒ Listable (e (Finite n))) ⇒ Listable (G e) where
  tiers = flip concatMapT tiers \(Natural x) →
    case someNatVal x of
      Nothing → error "foreachN: impossible"
      Just (SomeNat (_ ∷ Proxy n)) →
        cons2 \next (root ∷ Finite n) →
          G next root (Unfold (index next) root)

spec ∷ Spec
spec = pure ()
