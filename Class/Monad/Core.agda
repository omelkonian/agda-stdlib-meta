{-# OPTIONS --safe --without-K #-}
module Class.Monad.Core where

open import Agda.Primitive using () renaming (Set to Type; Setω to Typeω)
open import Level using (Level; suc; _⊔_)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Class.Functor.Core
open import Class.Applicative.Core

{-
Monad : (Type ℓ → Type ℓ) → Type (suc ℓ)
Monad {ℓ = ℓ} = RawMonad {f = ℓ}
open RawMonad ⦃ ... ⦄ public
  using (return; _>>=_; _>>_; _=<<_; _>=>_; _<=<_; join)
-}

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ; B : Type ℓ′; C : Type ℓ″; M : Type↑

record Monad (M : Type↑) : Typeω where
  infixl 1 _>>=_ _>>_ _≫=_ _≫_ _>=>_
  infixr 1 _=<<_ _=≪_ _<=<_

  field
    overlap ⦃ super ⦄ : Applicative M
    return : A → M A
    _>>=_  : M A → (A → M B) → M B

  _>>_ : M A → M B → M B
  m₁ >> m₂ = m₁ >>= λ _ → m₂

  _=<<_ : (A → M B) → M A → M B
  f =<< c = c >>= f

  _≫=_ = _>>=_; _≫_  = _>>_; _=≪_ = _=<<_

  _>=>_ : (A → M B) → (B → M C) → (A → M C)
  f >=> g = _=<<_ g ∘ f

  _<=<_ : (B → M C) → (A → M B) → (A → M C)
  g <=< f = f >=> g

  join : M (M A) → M A
  join m = m >>= id
open Monad ⦃...⦄ public

record Monad-Laws (M : Type↑) ⦃ _ : Monad M ⦄ : Typeω where
  field
    >>=-identityˡ : ∀ {A : Type ℓ} {B : Type ℓ′} {a : A} {h : A → M B} →
      (return a >>= h) ≡ h a
    >>=-identityʳ : ∀ {A : Type ℓ} (m : M A) →
      (m >>= return) ≡ m
    >>=-assoc : ∀ {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″} (m : M A) {g : A → M B} {h : B → M C} →
      ((m >>= g) >>= h) ≡ (m >>= (λ x → g x >>= h))
open Monad-Laws ⦃...⦄ public

record Lawful-Monad (M : Type↑) : Typeω where
  field ⦃ isMonad ⦄ : Monad M
        ⦃ hasMonadLaws ⦄ : Monad-Laws M
open Lawful-Monad ⦃...⦄ using () public
instance
  mkLawful-Monad : ⦃ _ : Monad M ⦄ → ⦃ Monad-Laws M ⦄ → Lawful-Monad M
  mkLawful-Monad = record {}

record Monad′ (M : Type[ ℓ ↝ ℓ′ ]) : Type (suc ℓ ⊔ ℓ′) where
  infixl 1 _>>=′_ _>>′_ _≫=′_ _≫′_ _>=>′_
  infixr 1 _=<<′_ _=≪′_ _<=<′_

  field
    return′ : A → M A
    _>>=′_  : M A → (A → M B) → M B

  _>>′_ : M A → M B → M B
  m₁ >>′ m₂ = m₁ >>=′ λ _ → m₂

  _=<<′_ : (A → M B) → M A → M B
  f =<<′ c = c >>=′ f

  _>=>′_ : (A → M B) → (B → M C) → (A → M C)
  f >=>′ g = _=<<′_ g ∘ f

  _<=<′_ : (B → M C) → (A → M B) → (A → M C)
  g <=<′ f = f >=>′ g

  _≫=′_ = _>>=′_; _≫′_ = _>>′_; _=≪′_ = _=<<′_

  -- join : M (M A) → M A
  -- join m = m >>= id

open Monad′ ⦃...⦄ public

record Monad₀ (M : Type↑) : Typeω where
  field ⦃ isMonad ⦄ : Monad M
        ⦃ isApplicative₀ ⦄ : Applicative₀ M
open Monad₀ ⦃...⦄ using () public
instance
  mkMonad₀ : ⦃ Monad M ⦄ → ⦃ Applicative₀ M ⦄ → Monad₀ M
  mkMonad₀ = record {}

record Monad⁺ (M : Type↑) : Typeω where
  field ⦃ isMonad ⦄ : Monad M
        ⦃ isAlternative ⦄ : Alternative M
open Monad⁺ ⦃...⦄ using () public
instance
  mkMonad⁺ : ⦃ Monad M ⦄ → ⦃ Alternative M ⦄ → Monad⁺ M
  mkMonad⁺ = record {}
