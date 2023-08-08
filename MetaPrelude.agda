{-# OPTIONS --safe --without-K #-}

module MetaPrelude where

open import Level renaming (_⊔_ to _⊔ˡ_; suc to sucˡ; zero to zeroˡ) public
open import Function public

open import Data.Bool hiding (_≟_; _≤_; _≤?_; _<_; _<?_) public
open import Data.Empty public
open import Data.List hiding (align; alignWith; fromMaybe; map; zip; zipWith) public
open import Data.Maybe hiding (_>>=_; ap; align; alignWith; fromMaybe; map; zip; zipWith) public
open import Data.Unit hiding (_≟_) public
open import Data.Sum hiding (assocʳ; assocˡ; map; map₁; map₂; reduce; swap) public
open import Data.Product hiding (assocʳ; assocˡ; map; map₁; map₂; swap; zip) public
open import Data.Nat hiding (_≟_; _≤_; _≤?_; _<_; _<?_; _≤ᵇ_; _≡ᵇ_) public
open import Data.String using (String; _<+>_) public

open import Relation.Binary.PropositionalEquality hiding (preorder; setoid; [_]; module ≡-Reasoning; decSetoid) public

lookupᵇ : {A B : Set} → (A → A → Bool) → List (A × B) → A → Maybe B
lookupᵇ f [] n = nothing
lookupᵇ f ((k , v) ∷ l) n = if f k n then just v else lookupᵇ f l n

open import Data.Fin
open import Data.List

zipWithIndex : {A B : Set} → (ℕ → A → B) → List A → List B
zipWithIndex f l = zipWith f (upTo $ length l) l

enumerate : {A : Set} → List A → List (ℕ × A)
enumerate = zipWithIndex _,_
