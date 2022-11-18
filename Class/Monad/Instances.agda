{-# OPTIONS --safe --without-K #-}
module Class.Monad.Instances where

open import Agda.Primitive using () renaming (Set to Type; Setω to Typeω)
open import Level using (Level)
open import Function using (_∘_; flip)

open import Data.List as L using (List; _++_; _∷_; []; concatMap; [_])
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Reflection using (TC)

open import Class.Functor.Core
open import Class.Applicative.Core
open import Class.Applicative.Instances
open import Class.Monad.Core

private variable ℓ ℓ′ ℓ″ : Level; M : Type↑

instance
  Monad-Maybe : Monad Maybe
  Monad-Maybe = λ where
    .return → pure
    ._>>=_ m f → maybe f nothing m

  MonadLaws-Maybe : Monad-Laws Maybe
  MonadLaws-Maybe = λ where
    .>>=-identityˡ → refl
    .>>=-identityʳ → λ where
      (just _) → refl
      nothing  → refl
    .>>=-assoc → λ where
      (just _) → refl
      nothing  → refl

  Monad-List : Monad List
  Monad-List = λ where
    .return → pure
    ._>>=_ → flip concatMap

  Monad-TC : Monad TC
  Monad-TC = record {M}
    where import Reflection as M

{- ** Id monad: provides us with forward composition as _>=>_,
                but breaks instance-resolution/typeclass-inference
module IdMonad where
  Id : Type ℓ → Type ℓ
  Id = id

  Monad-Id : Monad Id
  Monad-Id .return = id
  Monad-Id ._>>=_ = _|>_
-}

private
  _ : (return 5 >>= just) ≡ just 5
  _ = refl
  _ : (return 5 >>= just) ≡ just 5
  _ = >>=-identityʳ _

  _ : ⦃ _ : Lawful-Monad M ⦄ → (ℕ → M ℕ)
  _ = return

  itω : {A : Typeω} → ⦃ A ⦄ → A
  itω ⦃ a ⦄ = a

  _ : Lawful-Monad Maybe
  _ = itω
