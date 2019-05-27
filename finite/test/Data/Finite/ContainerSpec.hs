{-# LANGUAGE
    BlockArguments,
    GADTs,
    ScopedTypeVariables,
    TypeApplications,
    UnicodeSyntax
  #-}

module Data.Finite.ContainerSpec where

import Prelude hiding (lookup)
import Data.Finite (finites)
import Data.Finite.Class (Finitary (..))
import Data.Finite.Container
import Data.Finite.Util (foreachF, foreach, prop)
import Data.Proxy (Proxy (..))
import Test.Hspec (Spec, describe)

spec ∷ Spec
spec = do
  describe "encode" do
    prop "is index of original element" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ [a]) →
        reify xs \w → map encode w == finites

  describe "lookup" do
    prop "is original element" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ [a]) →
        reify xs \w → map lookup w == xs

  describe "IsFinite Witness" do
    prop "is bijection (1)" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ [a]) →
        reify xs \w → map (decode . encode) w == w

    prop "is bijection (2)" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ [a]) →
        reify xs \(_ ∷ [Index s]) →
          let ixs = finites @(Size s)
          in map (encode . decode  @(Index s)) ixs == ixs

    prop "respects comparison" $
      foreachF \(_ ∷ Proxy a) →
      foreach  \(xs ∷ [a]) →
        reify xs \w → and do
          x ← w
          y ← w
          pure (compare x y == compare (encode x) (encode y))
