{-# OPTIONS --safe --without-K #-}
--------------------------------------------------------------------------------
-- intro, intros: introduce one or many variables & continue with another tactic
--------------------------------------------------------------------------------

module Tactic.Intro where

open import Prelude
open import Meta

open import Class.Monad
open import Class.MonadTC.Instances

open import Reflection.Tactic
open import Reflection.Utils.TCI

private
  introHelper : ITactic → TC ⊤ → ITactic
  introHelper tac fail = do
    hole ← goalHole
    ty ← inferType hole
    case ty of λ where
      (pi argTy@(arg (arg-info v _) _) (abs x ty′)) → do
        hole′ ← extendContext (x , argTy) (newMeta ty′)
        unifyStrict (hole , ty) (lam v (abs "_" hole′))
        extendContext (x , argTy) (runWithHole hole′ tac)
      _ → fail

intro : ITactic → ITactic
intro tac = inDebugPath "intro" (introHelper tac (error1 "intro: not a pi type"))

intros : ℕ → ITactic → ITactic
intros 0       tac = error1 "intros: no more fuel"
intros (suc k) tac = inDebugPath "intros" (introHelper (intros k tac) tac)

private
  open import Tactic.Assumption
  open import Tactic.Defaults

  macro
    intro→fill : ⦃ TCOptions ⦄ → Tactic
    intro→fill = initTac ⦃ defaultTCOptionsI ⦄ $ intro assumption'

    intros→fill : ⦃ TCOptions ⦄ → Tactic
    intros→fill = initTac ⦃ defaultTCOptionsI ⦄ $ intros 5 assumption'

  _ : ℕ → ℕ
  _ = intro→fill

  _ : ∀ (n : ℕ) → ℕ
  _ = intro→fill

  _ : ∀ {n : ℕ} → ℕ
  _ = intros→fill

  _ : ∀ ⦃ n : ℕ ⦄ → ℕ
  _ = intros→fill

  _ : Bool → Bool
  _ = intro→fill

  _ : ∀ (n : Bool) → Bool
  _ = intro→fill

  _ : ∀ {n : Bool} → Bool
  _ = intros→fill

  _ : ℕ → Bool → ℕ
  _ = intros→fill

  _ : Bool → ℕ → ℕ
  _ = intros→fill

  _ : (n : ℕ) → Bool → ℕ
  _ = intros→fill

  _ : ℕ → (b : Bool) → ℕ
  _ = intros→fill

  _ : (n : ℕ) (b : Bool) → ℕ
  _ = intros→fill

  _ : (n : ℕ) {b : Bool} → ℕ
  _ = intros→fill

  _ : {n : ℕ} {b : Bool} → ℕ
  _ = intros→fill

  _ : ∀ {n : Bool} → Bool
  _ = intros→fill

  _ : {n : ℕ} (b : Bool) → Bool
  _ = intros→fill

  _ : (n : ℕ) → Bool → Bool
  _ = intros→fill

  _ : {b : Bool} {n : ℕ} → ℕ
  _ = intros→fill

  _ : (b : Bool) {n : ℕ} → ℕ
  _ = intros→fill

  _ : ∀ {b : Bool} (n : ℕ) → ℕ
  _ = intros→fill

  _ : ∀ (b : Bool) (n : ℕ) → Bool
  _ = intros→fill

  open import Data.List.Membership.Propositional

  _ : ∀ {x : ℕ} {xs} → x ∈ xs → x ∈ xs
  _ = intro→fill

  _ : ∀ {x y : ℕ} {xs ys} → x ∈ xs → y ∈ ys → x ∈ xs
  _ = intros→fill

  _ : ∀ {x y : ℕ} {xs} → x ∈ xs → y ∈ xs → y ∈ xs
  _ = intros→fill
