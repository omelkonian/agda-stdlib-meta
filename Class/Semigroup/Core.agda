{-# OPTIONS --safe --without-K #-}
module Class.Semigroup.Core where

open import Agda.Primitive using () renaming (Set to Type)
open import Level using (Level; _⊔_)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; sym)
import Algebra.Definitions as Alg

private variable ℓ ℓ′ : Level

record Semigroup (A : Type ℓ) : Type ℓ where
  infixr 5 _◇_ _<>_
  field _◇_ : A → A → A
  _<>_ = _◇_
open Semigroup ⦃...⦄ public

record SemigroupLaws (A : Type ℓ) ⦃ _ : Semigroup A ⦄ (_≈_ : Rel A ℓ′)
  : Type (ℓ ⊔ ℓ′) where
  open Alg _≈_
  field ◇-comm   : Commutative _◇_
        ◇-assocʳ : Associative _◇_
open SemigroupLaws ⦃...⦄ public

SemigroupLaws≡ : (A : Type ℓ) → ⦃ Semigroup A ⦄ → Type ℓ
SemigroupLaws≡ A = SemigroupLaws A _≡_

module _ {A : Type ℓ} ⦃ _ : Semigroup A ⦄ ⦃ _ : SemigroupLaws≡ A ⦄ where
  ◇-assocˡ : ∀ (x y z : A) → (x ◇ (y ◇ z)) ≡ ((x ◇ y) ◇ z)
  ◇-assocˡ x y z = sym (◇-assocʳ x y z)
