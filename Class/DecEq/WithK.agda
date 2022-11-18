{-# OPTIONS --safe #-}
module Class.DecEq.WithK where

open import Agda.Primitive using () renaming (Set to Type)
open import Level using (Level)
open import Data.Product
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality

open import Class.DecEq.Core

private variable ℓ ℓ′ : Level

module _ {A : Type ℓ} ⦃ _ : DecEq A ⦄ where
  ≟-refl : ∀ (x : A) → (x ≟ x) ≡ yes refl
  ≟-refl x with refl , p ← dec-yes (x ≟ x) refl = p

  DecEq-Σ : ∀ {B : A → Type ℓ′} ⦃ _ : ∀ {x} → DecEq (B x) ⦄ → DecEq (Σ A B)
  DecEq-Σ ._≟_ (x , y) (x′ , y′)
    with x ≟ x′
  ... | no ¬p    = no λ where refl → ¬p refl
  ... | yes refl
    with y ≟ y′
  ... | no ¬p    = no λ where refl → ¬p refl
  ... | yes refl = yes refl
