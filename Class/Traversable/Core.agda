{-# OPTIONS --safe --without-K #-}
module Class.Traversable.Core where

open import Agda.Primitive using () renaming (Set to Type; Setω to Typeω)
open import Level using (Level)
open import Function using (_∘_)

open import Class.Functor.Core
open import Class.Applicative.Core
open import Class.Monad.Core
open import Class.Foldable.Core

private variable
  ℓ ℓ′ : Level
  A : Type ℓ; B : Type ℓ′; M : Type↑

record TraversableA (F : Type↑) ⦃ _ : Functor F ⦄ ⦃ _ : Foldable F ⦄ : Typeω where
  field sequenceA : ⦃ Applicative M ⦄ → F (M A) → M (F A)

  traverseA : ⦃ Applicative M ⦄ → (A → M B) → F A → M (F B)
  traverseA f = sequenceA ∘ fmap f
open TraversableA ⦃...⦄ public

record TraversableM (F : Type↑) ⦃ _ : Functor F ⦄ ⦃ _ : Foldable F ⦄ : Typeω where
  field sequenceM : ⦃ Monad M ⦄ → F (M A) → M (F A)

  traverseM : ⦃ Monad M ⦄ → (A → M B) → F A → M (F B)
  traverseM f = sequenceM ∘ fmap f
open TraversableM ⦃... ⦄ public
