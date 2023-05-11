{-# OPTIONS --safe --without-K #-}
module Class.Traversable.Instances where

open import Function using (_∘_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List; open import Data.List.NonEmpty

open import Class.Functor.Core
open import Class.Functor.Instances
open import Class.Monad
open import Class.Traversable.Core

open import Level using (Level)
private variable ℓ ℓ′ : Level

instance
  Traversable-Maybe : Traversable Maybe
  Traversable-Maybe .sequence nothing  = return nothing
  Traversable-Maybe .sequence (just x) = x >>= return ∘ just

  Traversable-List : Traversable List
  Traversable-List .sequence = go
    where go = λ where
      []       → return []
      (m ∷ ms) → do x ← m; xs ← go ms; return (x ∷ xs)

  Traversable-List⁺ : Traversable List⁺
  Traversable-List⁺ .sequence (m ∷ ms) = do x ← m; xs ← sequence ms; return (x ∷ xs)
