{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# LANGUAGE
    BlockArguments,
    ScopedTypeVariables,
    TypeApplications,
    TypeOperators,
    UnicodeSyntax
  #-}

module Data.Finite.ClassSpec where

import Data.Finite (Finite)
import Data.Finite.Class
import Data.Finite.Util ( describeFinite, describeFinite1, describeFinite2
                        , foreachF, foreachN, foreach, prop
                        )
import Data.Proxy (Proxy (..))
import Data.These (These (..))
import Data.Void (Void)
import GHC.TypeLits (type (^))
import Test.Hspec (Spec, describe)

spec ∷ Spec
spec = do
  describeFinite @Void "Void"
  describeFinite @() "()"
  describeFinite @Bool "Bool"
  describeFinite @(Proxy ()) "Proxy"
  describeFinite1 @Maybe "Maybe"
  describeFinite2 @Either "Either"
  describeFinite2 @(,) "(,)"
  describeFinite2 @These "These"
  describeFinite2 @Fun "Fun"

  describe "memoize" do
    prop "is identity" $
      foreachF \(_ ∷ Proxy a) →
      foreachF \(_ ∷ Proxy b) →
      foreach  \(Fun f ∷ Fun a b) →
        Fun (memoize f) == Fun f

  describe "combinePower" do
    prop "is inverse of separatePower" $
      foreachN \(_ ∷ Proxy m) →
      foreachN \(_ ∷ Proxy n) →
      foreach  \(x ∷ Finite (m ^ n)) →
        combinePower @n @m (separatePower x) == x

  describe "separatePower" do
    prop "is inverse of combinePower" $
      foreachN \(_ ∷ Proxy m) →
      foreachN \(_ ∷ Proxy n) →
      foreach  \(Fun f ∷ Fun (Finite m) (Finite n)) →
        Fun (separatePower (combinePower f)) == Fun f
