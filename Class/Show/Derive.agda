-- {-# OPTIONS --safe --without-K #-}
module Class.Show.Derive where

open import Class.Show.Core
open import Generics

instance
  Derive-Show : Derivable Show
  Derive-Show = NOT_IMPLEMENTED
    where postulate NOT_IMPLEMENTED : ∀ {ℓ} {A : Set ℓ} → A
