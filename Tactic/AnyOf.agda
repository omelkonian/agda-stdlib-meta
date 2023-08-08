{-# OPTIONS --safe --without-K #-}
--------------------------------------------------------------------------------
-- anyOf: take the first term that type checks
--------------------------------------------------------------------------------

module Tactic.AnyOf where

open import MetaPrelude
open import Meta

open import Reflection.Utils.TCI
open import Reflection.Tactic

open import Class.Monad
open import Class.MonadError.Instances
open import Class.MonadTC.Instances

anyOf' : List Term → ITactic
anyOf' = inDebugPath "anyOf" ∘
  foldl (λ x t → catch (debugLog ("Attempting: " ∷ᵈ t ∷ᵈ []) >> unifyWithGoal t >> debugLog ("Success with: " ∷ᵈ t ∷ᵈ [])) (λ _ → x))
    (logAndError1 "None of the provded terms solve the goal!")

anyOfⁿ : List Name → ITactic
anyOfⁿ = inDebugPath "anyOf" ∘
  foldl (λ x n → catch (debugLog ("Attempting: " ∷ᵈ n ∷ᵈ []) >> unifyWithGoal (n ∙) >> debugLog ("Success with: " ∷ᵈ n ∷ᵈ [])) (λ _ → x))
    (logAndError1 "None of the provded terms solve the goal!")

module _ ⦃ _ : TCOptions ⦄ where
  anyOfᵗ : List Term → Tactic
  anyOfᵗ l = initTac $ anyOf' l

  anyOfⁿᵗ : List Name → Tactic
  anyOfⁿᵗ l = initTac $ anyOfⁿ l

  macro
    anyOf = anyOfᵗ
