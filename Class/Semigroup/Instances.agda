{-# OPTIONS --safe --without-K #-}
module Class.Semigroup.Instances where

open import Agda.Primitive using () renaming (Set to Type)
open import Level using (Level)
open import Function using (_∋_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
import Algebra.Definitions as Alg

open import Data.Product using (_,_; ∃)
open import Data.List using (List; _++_)
open import Data.List.NonEmpty using (List⁺; _⁺++⁺_)
open import Data.Vec as V using (Vec)
open import Data.String as Str using (String)
open import Data.Maybe using (Maybe; just; nothing)

open import Class.Semigroup.Core

private variable
  ℓ : Level
  A : Type ℓ

instance
  Semigroup-List : Semigroup (List A)
  Semigroup-List ._◇_ = _++_

  Semigroup-List⁺ : Semigroup (List⁺ A)
  Semigroup-List⁺ ._◇_ = _⁺++⁺_

  Semigroup-∃Vec : Semigroup (∃ (Vec A))
  Semigroup-∃Vec ._◇_ (_ , v) (_ , v′) = _ , (v V.++ v′)

  Semigroup-String : Semigroup String
  Semigroup-String ._◇_ = Str._++_

  Semigroup-Maybe : ⦃ Semigroup A ⦄ → Semigroup (Maybe A)
  Semigroup-Maybe ._◇_ = λ where
    (just x) (just y) → just (x ◇ y)
    (just x) nothing  → just x
    nothing  m        → m

  SemigroupLaws-Maybe : ⦃ sm : Semigroup A ⦄ → ⦃ SemigroupLaws≡ A ⦄ → SemigroupLaws≡ (Maybe A)
  SemigroupLaws-Maybe {A = A} = record {◇-assocʳ = p; ◇-comm = q}
    where
      open Alg {A = Maybe A} _≡_

      p : Associative (_◇_ {A = Maybe A})
      p (just _) (just _) (just _) = cong just (◇-assocʳ _ _ _)
      p (just _) (just _) nothing  = refl
      p (just _) nothing  _ = refl
      p nothing  (just _) _ = refl
      p nothing  nothing  _ = refl

      q : Commutative (_◇_ {A = Maybe A})
      q (just x) (just y) = cong just (◇-comm x y)
      q (just _) nothing  = refl
      q nothing  (just _) = refl
      q nothing  nothing  = refl


-- ** nats
module _ where
  open import Data.Nat
  open import Data.Nat.Properties

  Semigroup-ℕ-+ = Semigroup ℕ ∋ λ where ._◇_ → _+_
  SemigroupLaws-ℕ-+ = SemigroupLaws ℕ _≡_ ∋
    record {◇-assocʳ = +-assoc; ◇-comm = +-comm}
    where instance _ = Semigroup-ℕ-+

  Semigroup-ℕ-* = Semigroup ℕ ∋ λ where ._◇_ → _*_
  SemigroupLaws-ℕ-* = SemigroupLaws ℕ _≡_ ∋
    record {◇-assocʳ = *-assoc; ◇-comm = *-comm}
    where instance _ = Semigroup-ℕ-*

-- ** integers
module _ where
  open import Data.Integer
  open import Data.Integer.Properties

  Semigroup-ℤ-+ = Semigroup ℤ ∋ λ where ._◇_ → _+_
  SemigroupLaws-ℤ-+ = SemigroupLaws ℤ _≡_ ∋
    record {◇-assocʳ = +-assoc; ◇-comm = +-comm}
    where instance _ = Semigroup-ℤ-+

  Semigroup-ℤ-* = Semigroup ℤ ∋ λ where ._◇_ → _*_
  SemigroupLaws-ℤ-* = SemigroupLaws ℤ _≡_ ∋
    record {◇-assocʳ = *-assoc; ◇-comm = *-comm}
    where instance _ = Semigroup-ℤ-*
