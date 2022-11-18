{-# OPTIONS --safe --without-K #-}
module Class.Functor.Instances where

open import Agda.Primitive using () renaming (Set to Type)
open import Level using (Level)
open import Function using (_∋_; id; _∘_; flip)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
import Algebra.Definitions as Alg

open import Data.Product using (_,_; ∃; -,_)
open import Data.List as L using (List; _++_; _∷_; [])
open import Data.List.NonEmpty as LNE using (List⁺; _⁺++⁺_; _∷_)
open import Data.Vec as V using (Vec; _∷_; [])
open import Data.String as Str using (String)
open import Data.Maybe as M using (Maybe; just; nothing)

open import Class.Functor.Core

private variable ℓ ℓ′ ℓ″ : Level

instance
  Functor-Maybe : Functor Maybe
  Functor-Maybe ._<$>_ = M.map

  FunctorLaws-Maybe : FunctorLaws Maybe
  FunctorLaws-Maybe = λ where
    .fmap-id → λ where (just _) → refl; nothing → refl
    .fmap-∘  → λ where (just _) → refl; nothing → refl

  Functor-List : Functor List
  Functor-List ._<$>_ = L.map

  FunctorLaws-List : FunctorLaws List
  FunctorLaws-List = record {fmap-id = p; fmap-∘ = q}
    where
      p : ∀ {A : Type ℓ} (x : List A) → fmap id x ≡ x
      p = λ where
        [] → refl
        (x ∷ xs) → cong (x ∷_) (p xs)

      q : ∀ {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″} {f : B → C} {g : A → B} (x : List A) →
        fmap (f ∘ g) x ≡ (fmap f ∘ fmap g) x
      q {f = f}{g} = λ where
        [] → refl
        (x ∷ xs) → cong (f (g x) ∷_) (q xs)

  Functor-List⁺ : Functor List⁺
  Functor-List⁺ ._<$>_ = LNE.map

  Functor-Vec : ∀ {n} → Functor (flip Vec n)
  Functor-Vec ._<$>_ = V.map

  open import Reflection
  open import Reflection.Meta

  Functor-TC : Functor TC
  Functor-TC = record {R}
    where import Reflection.TypeChecking.Monad.Syntax as R

  Functor-Abs : Functor  Abs
  Functor-Abs = record {R}
    where import Reflection.Abstraction as R renaming (map to _<$>_)

  Functor-Arg : Functor Arg
  Functor-Arg = record {R}
    where import Reflection.Argument as R renaming (map to _<$>_)

  Functor-∃Vec : Functor (∃ ∘ Vec)
  Functor-∃Vec ._<$>_ f (_ , xs) = -, (f <$> xs)

private
  open import Data.Nat

  _ : fmap suc (just 0) ≡ just 1
  _ = refl

  _ : fmap suc (List ℕ ∋ 0 ∷ 1 ∷ 2 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ [])
  _ = refl

  _ : fmap suc (List⁺ ℕ ∋ 0 ∷ 1 ∷ 2 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ [])
  _ = refl

  _ : fmap suc (Vec ℕ 3 ∋ 0 ∷ 1 ∷ 2 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ [])
  _ = refl

  _ : fmap suc (∃ (Vec ℕ) ∋ -, 0 ∷ 1 ∷ 2 ∷ []) ≡ (-, 1 ∷ 2 ∷ 3 ∷ [])
  _ = refl
