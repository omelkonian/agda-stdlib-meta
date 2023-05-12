{-# OPTIONS --safe --without-K #-}
module Tactic.Defaults where

open import Prelude

open import Class.MonadTC
open import Reflection.Debug

-- There should only ever be one instance, with this being convenient
-- to tweak all at once
instance
  defaultTCOptionsI = record
    { debug = record defaultDebugOptions { selection = All }
    ; fuel  = ("reduceDec/constrs" , 5) ∷ [] }
