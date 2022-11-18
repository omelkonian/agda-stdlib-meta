{-# OPTIONS --safe --without-K #-}
module Class.Monoid.Core where

open import Agda.Primitive using () renaming (Set to Type)
open import Level using (Level; _⊔_)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; sym)
import Algebra.Definitions as Alg

open import Data.Product using (proj₁; proj₂)

open import Class.Semigroup.Core

private variable ℓ ℓ′ : Level

record Monoid (A : Type ℓ) : Type ℓ where
  field
    overlap ⦃ sm ⦄ : Semigroup A
    ε : A

open Monoid ⦃...⦄ public hiding (sm)

record MonoidLaws (A : Type ℓ) ⦃ _ : Monoid A ⦄ (_~_ : Rel A ℓ′) : Type (ℓ ⊔ ℓ′) where
  open Alg _~_
  field ε-identity : Identity ε _◇_

  ε-identityˡ : LeftIdentity ε _◇_
  ε-identityˡ = ε-identity .proj₁

  ε-identityʳ : RightIdentity ε _◇_
  ε-identityʳ = ε-identity .proj₂
open MonoidLaws ⦃...⦄ public

MonoidLaws≡ : (A : Type ℓ) → ⦃ Monoid A ⦄ → Type ℓ
MonoidLaws≡ A = MonoidLaws A _≡_
