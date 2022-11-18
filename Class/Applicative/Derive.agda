-- {-# OPTIONS --safe --without-K #-}
module Class.Applicative.Derive where

open import Agda.Primitive
open import Class.Applicative.Core
open import Generics

instance
  Derive-Applicative : Derivable¹ Applicative
  Derive-Applicative = NOT_IMPLEMENTED
    where postulate NOT_IMPLEMENTED : ∀ {A : Setω} → A
