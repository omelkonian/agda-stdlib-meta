-- {-# OPTIONS --safe --without-K #-}
module Class.Foldable.Derive where

open import Agda.Primitive
open import Class.Foldable.Core
open import Generics

instance
  Derive-Foldable : Derivable¹ Foldable
  Derive-Foldable = NOT_IMPLEMENTED
    where postulate NOT_IMPLEMENTED : ∀ {A : Setω} → A
