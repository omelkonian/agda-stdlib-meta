-- {-# OPTIONS --safe --without-K #-}
module Class.DecEq.Derive where

open import Class.DecEq.Core
open import Generics

instance
  Derive-DecEq : Derivable DecEq
  Derive-DecEq = NOT_IMPLEMENTED
    where postulate NOT_IMPLEMENTED : ∀ {ℓ} {A : Set ℓ} → A
