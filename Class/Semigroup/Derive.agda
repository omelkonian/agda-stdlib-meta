-- {-# OPTIONS --safe --without-K #-}
module Class.Semigroup.Derive where

open import Class.Semigroup.Core
open import Reflection.Utils.Debug

instance
  Derive-Semigroup : Derivable Semigroup
  Derive-Semigroup = NOT_IMPLEMENTED
    where postulate NOT_IMPLEMENTED : ∀ {ℓ} {A : Set ℓ} → A
