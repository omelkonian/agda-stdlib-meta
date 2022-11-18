{-# OPTIONS --safe --without-K #-}
module Class.Foldable.Core where

open import Agda.Primitive using () renaming (Set to Type; Setω to Typeω)
open import Level using (Level)

open import Class.Functor.Core
open import Class.Monoid.Core

private variable ℓ ℓ′ : Level

record Foldable (F : Type↑) : Typeω where
  field foldMap : ∀ {A : Type ℓ} {M : Type ℓ′} → ⦃ Monoid M ⦄ → (A → M) → F A → M
open Foldable ⦃...⦄ public
