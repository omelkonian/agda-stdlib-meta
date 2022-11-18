{-# OPTIONS --safe --without-K #-}
module Class.Applicative.Core where

open import Agda.Primitive using () renaming (Set to Type; Setω to Typeω)
open import Level using (Level)
open import Function using (const; flip; id; _∘_; constᵣ)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; foldr)
open import Data.List.NonEmpty using (List⁺; foldr₁)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Class.Functor.Core

{-
Applicative : (Type ℓ → Type ℓ) → Type (lsuc ℓ)
Applicative {ℓ = ℓ} = RawApplicative {f = ℓ}
open RawApplicative ⦃ ... ⦄ public
  using (pure)
  renaming ( _⊛_ to _<*>_; _<⊛_ to _<*_ ; _⊛>_ to _*>_)
-}

private variable
  ℓ : Level
  A B C : Type ℓ
  M F : Type↑

-- record Applicative (F : Type ℓ → Type ℓ′) : Type (lsuc ℓ ⊔ₗ ℓ′) where
record Applicative (F : Type↑) : Typeω where
  infixl 4 _<*>_ _⊛_ _<*_ _<⊛_ _*>_ _⊛>_
  infix  4 _⊗_

  field
    overlap ⦃ super ⦄ : Functor F
    pure : A → F A
    _<*>_  : F (A → B) → F A → F B
  _⊛_ = _<*>_

  _<*_ : F A → F B → F A
  x <* y = const <$> x ⊛ y

  _*>_ : F A → F B → F B
  x *> y = constᵣ <$> x ⊛ y

  _<⊛_ = _<*_; _⊛>_ = _*>_

  _⊗_ : F A → F B → F (A × B)
  x ⊗ y = (_,_) <$> x ⊛ y

  zipWithA : (A → B → C) → F A → F B → F C
  zipWithA f x y = f <$> x ⊛ y

  zipA : F A → F B → F (A × B)
  zipA = zipWithA _,_

open Applicative ⦃...⦄ public

record Applicative₀ (F : Type↑) : Typeω where
  field
    overlap ⦃ super ⦄ : Applicative F
    ε₀ : F A
open Applicative₀ ⦃...⦄ public

record Alternative (F : Type↑) : Typeω where
  infixr 3 _<|>_
  field _<|>_ : F A → F A → F A
    -- overlap ⦃ ap₀ ⦄ : Applicative₀ F
open Alternative ⦃...⦄ {- hiding (ap₀) -} public

infix -1 ⋃⁺_ ⋃_

⋃⁺_ : ⦃ Alternative F ⦄ → List⁺ (F A) → F A
⋃⁺_ = foldr₁ _<|>_

⋃_ : ⦃ Applicative₀ F ⦄ → ⦃ Alternative F ⦄ → List (F A) → F A
⋃_ = foldr _<|>_ ε₀
