-- {-# OPTIONS --safe --without-K #-}
module Class.Monoid.Derive where

open import Class.Monoid.Core
open import Generics

instance
  Derive-Monoid : Derivable Monoid
  Derive-Monoid = NOT_IMPLEMENTED
    where postulate NOT_IMPLEMENTED : ∀ {ℓ} {A : Set ℓ} → A
