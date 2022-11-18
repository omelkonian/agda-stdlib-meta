-- {-# OPTIONS --safe --without-K #-}
module Class.Monad.Derive where

open import Agda.Primitive
open import Class.Monad.Core
open import Generics

instance
  Derive-Monad : Derivable¹ Monad
  Derive-Monad = NOT_IMPLEMENTED
    where postulate NOT_IMPLEMENTED : ∀ {A : Setω} → A
