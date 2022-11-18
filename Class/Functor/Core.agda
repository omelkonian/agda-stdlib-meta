{-# OPTIONS --safe --without-K #-}
module Class.Functor.Core where

open import Agda.Primitive using () renaming (Set to Type; Setω to Typeω)
open import Level using (Level; suc; _⊔_)
open import Function using (const; flip; id; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_)

{-
Functor : (Type ℓ → Type ℓ) → Type (lsuc ℓ)
Functor {ℓ = ℓ} = RawFunctor {ℓ = ℓ} {ℓ′ = ℓ}
open RawFunctor ⦃...⦄ public
-}

private variable
  a b c : Level
  A : Type a; B : Type b; C : Type c

Type[_↝_] : ∀ ℓ ℓ′ → Type (suc ℓ ⊔ suc ℓ′)
Type[ ℓ ↝ ℓ′ ] = Type ℓ → Type ℓ′

Type↑ : Typeω
Type↑ = ∀ {ℓ} → Type[ ℓ ↝ ℓ ]

record Functor (F : Type↑) : Typeω where
  infixl 4 _<$>_ _<$_
  infixl 1 _<&>_

  field _<$>_ : (A → B) → F A → F B
  fmap = _<$>_

  _<$_ : A → F B → F A
  x <$ y = const x <$> y

  _<&>_ : F A → (A → B) → F B
  _<&>_ = flip _<$>_
open Functor ⦃...⦄ public

record FunctorLaws (F : Type↑) ⦃ _ : Functor F ⦄ : Typeω where
  field
    -- preserves identity morphisms
    fmap-id : ∀ {A : Type a} (x : F A) →
      fmap id x ≡ x
    -- preserves composition of morphisms
    fmap-∘  : ∀ {A : Type a} {B : Type b} {C : Type c}
                {f : B → C} {g : A → B} (x : F A) →
      fmap (f ∘ g) x ≡ (fmap f ∘ fmap g) x
open FunctorLaws ⦃...⦄ public
