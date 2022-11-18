------------------------
-- ** Monadic utilities.

{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using () renaming (Set to Type)
open import Level using (Level)
open import Function using (_∘_)

open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; if_then_else_; true; false)
open import Data.List using (List; []; _∷_; concat; [_]; _++_)
open import Data.Maybe using (Maybe; just; fromMaybe)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Class.Functor.Core
open import Class.Applicative.Core
open import Class.Applicative.Instances
open import Class.Monad.Core
open import Class.Monad.Instances

module Class.Monad.Utils {M : Type↑} ⦃ _ : Monad M ⦄ where

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ; B : Type ℓ′; C : Type ℓ″

mapM : (A → M B) → List A → M (List B)
mapM f []       = return []
mapM f (x ∷ xs) = ⦇ f x ∷ mapM f xs ⦈

concatMapM : (A → M (List B)) → List A → M (List B)
concatMapM f xs = concat <$> mapM f xs

forM : List A → (A → M B) → M (List B)
forM []       _ = return []
forM (x ∷ xs) f = ⦇ f x ∷ forM xs f ⦈

concatForM : List A → (A → M (List B)) → M (List B)
concatForM xs f = concat <$> forM xs f

return⊤ void : M A → M ⊤
return⊤ k = k ≫ return tt
void = return⊤

filterM : (A → M Bool) → List A → M (List A)
filterM _ [] = return []
filterM p (x ∷ xs) = do
  b ← p x
  ((if b then [ x ] else []) ++_) <$> filterM p xs

-- traverse : ∀ {A B : Type} {M : Type → Type} → ⦃ Applicative M ⦄ → ⦃ Monad M ⦄ → (A → M B) → List A → M (List B)
-- traverse f = λ where
--   [] → return []
--   (x ∷ xs) → ⦇ f x ∷ traverse f xs ⦈

do-pure : ∀ {A : Type ℓ} {x : A} {mx : Maybe A} {f : A → Bool}
  → mx ≡ just x
  → f x ≡ true
  → fromMaybe false (mx >>= pure ∘ f) ≡ true
do-pure refl f≡ rewrite f≡ = refl
