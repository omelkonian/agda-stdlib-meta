{-# OPTIONS --safe --without-K #-}
module Class.DecEq.Instances where

open import Agda.Primitive using () renaming (Set to Type)
open import Level using (Level)
open import Function using (_∋_; _∘_; _$_)

open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
import Data.Product.Properties as Pr
open import Data.Sum using (_⊎_)
open import Data.These using (These)
open import Data.Maybe using (Maybe)
open import Data.List as L using (List)
import Data.List.Properties as L
open import Data.List.NonEmpty as LNE using (List⁺; _∷_)
open import Data.Vec using (Vec)
open import Data.Fin using (Fin)
open import Reflection using (Arg)

open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)

open import Class.DecEq.Core

private variable
  ℓ ℓ′ : Level
  A : Type ℓ; B : Type ℓ′

instance
  DecEq-⊤ = DecEq _ ∋ record {M}
    where import Data.Unit as M

  DecEq-Bool = DecEq _ ∋ record {M}
    where import Data.Bool as M

  DecEq-ℕ = DecEq _ ∋ record {M}
    where import Data.Nat as M

  DecEq-ℤ = DecEq _ ∋ record {M}
    where import Data.Integer as M

  DecEq-Char = DecEq _ ∋ record {M}
    where import Data.Char as M

  DecEq-String = DecEq _ ∋ record {M}
    where import Data.String as M

  DecEq-Fin : ∀ {n} → DecEq (Fin n)
  DecEq-Fin = record {M}
    where import Data.Fin as M

  DecEq-List : ⦃ DecEq A ⦄ → DecEq (List A)
  DecEq-List ._≟_ = M.≡-dec _≟_
    where import Data.List.Properties as M

  module _ ⦃ _ : DecEq A ⦄ where
    private
      ∷-injective : ∀ {x y : A} {xs ys} →
        x ∷ xs ≡ y LNE.∷ ys → x ≡ y × xs ≡ ys
      ∷-injective refl = (refl , refl)

    DecEq-List⁺ : DecEq (List⁺ A)
    DecEq-List⁺ ._≟_ (x ∷ xs) (y ∷ ys)
      with x ≟ y
    ... | no x≢y = no $ x≢y ∘ proj₁ ∘ ∷-injective
    ... | yes refl
      with xs ≟ ys
    ... | no xs≢ys = no $ xs≢ys ∘ proj₂ ∘ ∷-injective
    ... | yes refl = yes refl

    DecEq-Vec : ∀ {n} → DecEq (Vec A n)
    DecEq-Vec ._≟_ = M.≡-dec _≟_
      where import Data.Vec.Properties as M

    DecEq-Maybe : DecEq (Maybe A)
    DecEq-Maybe ._≟_ = M.≡-dec _≟_
      where import Data.Maybe.Properties as M

  module _ ⦃ _ : DecEq A ⦄ ⦃ _ : DecEq B ⦄ where

    DecEq-⊎ : DecEq (A ⊎ B)
    DecEq-⊎ ._≟_ = Sum.≡-dec _≟_ _≟_
      where import Data.Sum.Properties as Sum

    DecEq-These : DecEq (These A B)
    DecEq-These ._≟_ = M.≡-dec _≟_ _≟_
      where import Data.These.Properties as M

  -- ** reflection

  DecEq-Name = DecEq _ ∋ record {M}
    where import Reflection.Name as M

  DecEq-Term = DecEq _ ∋ record {M}
    where import Reflection.Term as M

  DecEq-Arg : ⦃ DecEq A ⦄ → DecEq (Arg A)
  DecEq-Arg ._≟_ = M.≡-dec _≟_
    where import Reflection.Argument as M

  DecEq-Vis = DecEq _ ∋ record {M}
    where import Reflection.Argument.Visibility as M
