{-# OPTIONS --safe --without-K #-}
module Class.Monoid.Instances where

open import Agda.Primitive using () renaming (Set to Type)
open import Level using (Level)
open import Function using (_∋_; _$_)
open import Relation.Binary.PropositionalEquality
import Algebra.Definitions as Alg

open import Data.Product using (_,_; ∃)
open import Data.List using (List; [])
import Data.List.Properties as L
open import Data.Vec as V using (Vec; [])
open import Data.String as Str using (String)
open import Data.Maybe using (Maybe; just; nothing)

open import Class.Semigroup.Core
open import Class.Semigroup.Instances
open import Class.Monoid.Core

private variable
  ℓ : Level
  A : Type ℓ

instance
  Monoid-List : Monoid (List A)
  Monoid-List .ε = []

  MonoidLaws-List : MonoidLaws≡ (List A)
  MonoidLaws-List = record {ε-identity = L.++-identityˡ , L.++-identityʳ}

  Monoid-Vec : Monoid (∃ (Vec A))
  Monoid-Vec .ε = 0 , []

  Monoid-String : Monoid String
  Monoid-String .ε = ""

  Monoid-Maybe : ⦃ Monoid A ⦄ → Monoid (Maybe A)
  Monoid-Maybe .ε = nothing

  MonoidLaws-Maybe : ⦃ m : Monoid A ⦄ → ⦃ MonoidLaws≡ A ⦄ → MonoidLaws≡ (Maybe A)
  MonoidLaws-Maybe {A = A} = record {ε-identity = p , q}
    where open Alg _≡_
          p = LeftIdentity ε  _◇_ ∋ λ _ → refl
          q = RightIdentity ε _◇_ ∋ λ where (just _) → refl; nothing → refl

-- ** nats
module _ where
  open import Data.Nat
  open import Data.Nat.Properties

  Monoid-ℕ-+ = Monoid ℕ ∋ λ where .ε → 0
    where instance _ = Semigroup-ℕ-+
  MonoidLaws-ℕ-+ = MonoidLaws≡ ℕ ∋ record {ε-identity = +-identityˡ , +-identityʳ}
    where instance _ = Monoid-ℕ-+

  Monoid-ℕ-* = Monoid ℕ ∋ λ where .ε → 1
    where instance _ = Semigroup-ℕ-*
  MonoidLaws-ℕ-* = MonoidLaws≡ ℕ ∋ record {ε-identity = *-identityˡ , *-identityʳ}
    where instance _ = Monoid-ℕ-*

-- ** integers
module _ where
  open import Data.Integer
  open import Data.Integer.Properties

  Monoid-ℤ-+ = Monoid ℤ ∋ λ where .ε → 0ℤ
    where instance _ = Semigroup-ℤ-+
  MonoidLaws-ℤ-+ = MonoidLaws≡ ℤ ∋ record {ε-identity = +-identityˡ , +-identityʳ}
    where instance _ = Monoid-ℤ-+

  Monoid-ℤ-* = Monoid ℤ ∋ λ where .ε → 1ℤ
    where instance _ = Semigroup-ℤ-*
  MonoidLaws-ℤ-* = MonoidLaws≡ ℤ ∋ record {ε-identity = *-identityˡ , *-identityʳ}
    where instance _ = Monoid-ℤ-*

-- ** maybes

module _ where
  open import Data.Maybe

  just-◇ˡ : ∀ {A : Type} ⦃ _ : Monoid A ⦄ ⦃ _ : MonoidLaws≡ A ⦄ (x : A) (mx : Maybe A) →
    just x ◇ mx ≡ just (x ◇ fromMaybe ε mx)
  just-◇ˡ x = λ where
    (just _) → refl
    nothing  → cong just $ sym $ ε-identityʳ x

  just-◇ʳ : ∀ {A : Type} ⦃ _ : Monoid A ⦄ ⦃ _ : MonoidLaws≡ A ⦄ (x : A) (mx : Maybe A) →
    mx ◇ just x ≡ just (fromMaybe ε mx ◇ x)
  just-◇ʳ x = λ where
    (just _) → refl
    nothing  → cong just $ sym $ ε-identityˡ x
