{-# LANGUAGE
    ImplicitParams,
    UnicodeSyntax
  #-}

module Weaver.Config where

data Config = Config
  { _debug    ∷ Bool
  , _semi     ∷ Bool
  , _minimize ∷ Bool
  }

debug ∷ (?config ∷ Config) ⇒ Bool
debug = _debug ?config

semi ∷ (?config ∷ Config) ⇒ Bool
semi = _semi ?config

minimize ∷ (?config ∷ Config) ⇒ Bool
minimize = _minimize ?config
