{-# OPTIONS --safe --without-K #-}
--------------------------------------------------------------------------------
-- eta: unify with an eta-expanded version of the argument
--------------------------------------------------------------------------------

module Tactic.Eta where

open import MetaPrelude
open import Meta

open import Data.List
open import Data.Fin

open import Class.Monad
open import Class.MonadTC.Instances
open import Class.Semigroup
open import Class.Show

open import Reflection.Tactic
open import Reflection.Utils
open import Reflection.Utils.TCI

saturate : Term → Args Type → TC Term
saturate f as = case f of λ where
  (def c as′) → return $ def c (as′ ++ as)
  _           → error1 $ "cannot saturate arbitrary expressions, only definitions"

macro
  η : ⦃ TCOptions ⦄ → Term → Tactic
  η f = initTac $ inDebugPath "eta" do
    debugLog ("f: " ∷ᵈ f ∷ᵈ [])
    ty ← inferType f -- =<< reduce f
    debugLog ("ty: " ∷ᵈ ty ∷ᵈ [])
    let as , _ = viewTy′ ty
    debugLog ("as: " ∷ᵈ show as ∷ᵈ [])
    f′ ← saturate f $ flip map (enumerate as) $ λ where
      (n , arg i _) → arg i (♯ (length as ∸ suc n))
    debugLog ("f′: " ∷ᵈ show f′ ∷ᵈ [])
    unifyWithGoal $ foldr (λ x t → Π[ "_" ∶ x ] t) f′ as


private
  module Test where
    open import Tactic.Defaults

    p : Set
    p = ∀ {n} → Fin n

    ∀p : ∀ {n} → Set
    ∀p {n} = Fin n

    _ : Set
    _ = η ∀p

    ∀kp : ∀ (m : ℕ) {n} → Set
    ∀kp _ {n} = Fin n

    _ : Set
    _ = η (∀kp 0)

    ∀k2p : ∀ (m : ℕ) {k : ℕ} {n} → Set
    ∀k2p _ {n = n} = Fin n

    _ : Set
    _ = η (∀k2p 0 {1})
