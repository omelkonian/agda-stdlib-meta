-- {-# OPTIONS --safe --without-K #-}
module Class.Functor.Derive where

open import Agda.Primitive
open import Class.Functor.Core
open import Reflection.Utils.Debug

instance
  Derive-Functor : Derivable¹ Functor
  Derive-Functor = NOT_IMPLEMENTED
    where postulate NOT_IMPLEMENTED : ∀ {A : Setω} → A
