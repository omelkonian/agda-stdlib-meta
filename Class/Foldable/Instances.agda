{-# OPTIONS --safe --without-K #-}
module Class.Foldable.Instances where

open import Data.Maybe; open import Data.List; open import Data.List.NonEmpty

open import Class.Semigroup.Core
open import Class.Semigroup.Instances
open import Class.Monoid.Core
open import Class.Monoid.Instances
open import Class.Foldable.Core

open import Level using (Level)
private variable ℓ ℓ′ : Level

instance
  Foldable-Maybe : Foldable Maybe
  Foldable-Maybe .foldMap f nothing  = ε
  Foldable-Maybe .foldMap f (just x) = f x

  Foldable-List : Foldable List
  Foldable-List .foldMap {A = A} {M = M} f = go
    where
      go : List A → M
      go = λ where
        [] → ε
        (x ∷ xs) → f x ◇ go xs

  Foldable-List⁺ : Foldable List⁺
  Foldable-List⁺ .foldMap f (x ∷ xs) = f x ◇ foldMap f xs
