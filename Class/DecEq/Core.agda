{-# OPTIONS --safe --without-K #-}
module Class.DecEq.Core where

open import Agda.Primitive using () renaming (Set to Type)
open import Data.Bool using (Bool; not)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋; dec-yes)
open import Relation.Binary using (DecidableEquality) renaming (Decidable to Decidable²)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

record DecEq {ℓ} (A : Type ℓ) : Type ℓ where
  field _≟_ : DecidableEquality A

  _==_ _≡ᵇ_ : A → A → Bool
  x == y = ⌊ x ≟ y ⌋
  _≡ᵇ_ = _==_

  _≠_ : A → A → Bool
  x ≠ y = not (x == y)

  infix 4 _≟_ _≡ᵇ_ _==_ _≠_
open DecEq ⦃...⦄ public
