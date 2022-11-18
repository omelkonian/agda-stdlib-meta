{-# OPTIONS --safe --without-K #-}

open import Prelude

open import Relation.Binary

module Interface.DecEq where

private variable ℓ : Level
                 A B : Set ℓ

record DecEq (A : Set ℓ) : Set ℓ where
  infix 4 _≟_
  field
    _≟_ : DecidableEquality A

open DecEq ⦃ ... ⦄ public

import Data.List.Properties
import Data.Maybe.Properties
import Data.Product.Properties
import Data.Sum.Properties
import Data.Nat
import Data.Unit
import Data.Integer

instance
  DecEq-⊥ : DecEq ⊥
  DecEq-⊥ ._≟_ = λ ()

  DecEq-⊤ : DecEq ⊤
  DecEq-⊤ ._≟_ = Data.Unit._≟_

  DecEq-ℕ : DecEq ℕ
  DecEq-ℕ ._≟_ = Data.Nat._≟_

  DecEq-ℤ : DecEq Data.Integer.ℤ
  DecEq-ℤ ._≟_ = Data.Integer._≟_

  DecEq-Maybe : ⦃ DecEq A ⦄ → DecEq (Maybe A)
  DecEq-Maybe ._≟_ = Data.Maybe.Properties.≡-dec _≟_

  DecEq-List : ⦃ DecEq A ⦄ → DecEq (List A)
  DecEq-List ._≟_ = Data.List.Properties.≡-dec _≟_

  DecEq-Product : ⦃ DecEq A ⦄ → ⦃ DecEq B ⦄ → DecEq (A × B)
  DecEq-Product ._≟_ = Data.Product.Properties.≡-dec _≟_ _≟_

  DecEq-Sum : ⦃ DecEq A ⦄ → ⦃ DecEq B ⦄ → DecEq (A ⊎ B)
  DecEq-Sum ._≟_ = Data.Sum.Properties.≡-dec _≟_ _≟_
