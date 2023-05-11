{-# OPTIONS --safe --without-K #-}
module Class.Traversable.Core where

open import Agda.Primitive using () renaming (Set to Type; Setω to Typeω)
open import Level using (Level)
open import Function using (_∘_)

open import Class.Functor.Core
open import Class.Monad

private variable
  ℓ ℓ′ : Level
  A : Type ℓ; B : Type ℓ′; M : Type↑

record Traversable (F : Type↑) ⦃ _ : Functor F ⦄ : Typeω where
  field sequence : ⦃ Monad M ⦄ → F (M A) → M (F A)

  traverse : ⦃ Monad M ⦄ → (A → M B) → F A → M (F B)
  traverse f = sequence ∘ fmap f
open Traversable ⦃... ⦄ public
