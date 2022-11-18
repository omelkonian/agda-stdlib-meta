{-# OPTIONS --safe --without-K #-}
module Class.Traversable.Instances where

open import Function using (_∘_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List; open import Data.List.NonEmpty

open import Class.Functor.Core
open import Class.Functor.Instances
open import Class.Applicative.Core
open import Class.Monad.Core
open import Class.Foldable.Core
open import Class.Foldable.Instances
open import Class.Traversable.Core

open import Level using (Level)
private variable ℓ ℓ′ : Level

instance
  TraversableA-Maybe : TraversableA  Maybe
  TraversableA-Maybe .sequenceA nothing  = pure nothing
  TraversableA-Maybe .sequenceA (just x) = ⦇ just x ⦈

  TraversableM-Maybe : TraversableM Maybe
  TraversableM-Maybe .sequenceM nothing  = return nothing
  TraversableM-Maybe .sequenceM (just x) = x >>= return ∘ just

  TraversableA-List : TraversableA List
  TraversableA-List .sequenceA = go
    where go = λ where
      []       → pure []
      (m ∷ ms) → ⦇ m ∷ go ms ⦈

  TraversableM-List : TraversableM List
  TraversableM-List .sequenceM = go
    where go = λ where
      []       → return []
      (m ∷ ms) → do x ← m; xs ← go ms; return (x ∷ xs)

  TraversableA-List⁺ : TraversableA List⁺
  TraversableA-List⁺ .sequenceA (m ∷ ms) = ⦇ m ∷ sequenceA ms ⦈

  TraversableM-List⁺ : TraversableM List⁺
  TraversableM-List⁺ .sequenceM (m ∷ ms) = do x ← m; xs ← sequenceM ms; return (x ∷ xs)
