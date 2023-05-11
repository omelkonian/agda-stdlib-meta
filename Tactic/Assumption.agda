{-# OPTIONS --safe --without-K #-}
--------------------------------------------------------------------------------
-- assumption: try to solve the goal with one of the available assumptions
--------------------------------------------------------------------------------

module Tactic.Assumption where

open import Prelude
open import Meta

open import Class.Monad
open import Class.Functor
open import Class.MonadError.Instances
open import Class.MonadReader.Instances
open import Class.MonadTC.Instances

open import Tactic.Helpers

open import Generics

instance
  _ = Functor-M

solve : ⦃ _ : DebugOptions ⦄ → Term → Tactic
solve t = initTac $ runSpeculative $ do
  inj₁ goal ← reader TCEnv.goal
    where _ → error1 "solve: Goal is not a term!"
  metas ← findMetas <$> checkType t goal
  if null metas
    then (_, true)  <$> unify goal t
    else (_, false) <$> error1 "Unsolved metavariables remaining!"

assumption' : ITactic
assumption' = inDebugPath "assumption" do
  c ← getContext
  foldl (λ x k → do
    catch (unifyWithGoal (♯ k) >> debugLog ("Success with: " ∷ᵈ ♯ k ∷ᵈ [])) (λ _ → x))
    (logAndError1 "No valid assumption!") (downFrom $ length c)

module _ ⦃ _ : DebugOptions ⦄ where
  macro
    assumption = initTac assumption'
    assumptionOpts = initTacOpts assumption'

private
  open import Tactic.Defaults
  module Test where
    test₁ : {A B : Set} → A → B → A
    test₁ a b = assumption
    
    test₂ : {A B : Set} → A → B → B
    test₂ a b = assumption
