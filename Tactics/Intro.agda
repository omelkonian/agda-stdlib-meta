{-# OPTIONS -v Generics:100 #-}
module Tactics.Intro where

open import Prelude

open import Class.Functor
open import Class.Monad
open import Class.Semigroup
open import Class.Show

open import Reflection hiding (_>>=_; _>>_; return)
open import Reflection.Syntax
open import Reflection.Tactic
open import Reflection.Utils.Debug
open import Reflection.Utils.TCM
open Debug ("Generics.Intros" , 100)

intro : Hole → Tactic → TC ⊤
intro hole k = do
  ty ← inferType hole
  case ty of λ where
    (pi argTy@(arg (arg-info v _) _) (abs x ty′)) → do
      printCurrentContext
      hole′ ← extendContext x argTy $ do
        hole′ ← newMeta ty′
        return hole′
      unifyStrict (hole , ty) (lam v (abs "_" hole′))
      extendContext x argTy $ do
        k hole′
    _ → k hole

{-# TERMINATING #-}
intros : Hole → Tactic → TC ⊤
intros hole k = do
  ty ← inferType hole
  case ty of λ where
    (pi argTy@(arg (arg-info v _) _) (abs x ty′)) → do
      print $ "\t* " ◇ show argTy
      printCurrentContext
      hole′ ← extendContext x argTy $ do
        hole′ ← newMeta ty′
        return hole′
      unifyStrict (hole , ty) (lam v (abs "_" hole′))
      extendContext x argTy $ do
        intros hole′ k
    _ → k hole

private
  fillFromContext : Tactic
  fillFromContext hole = do
    ty ← inferType hole
    ctx ← getContext
    printContext ctx
    let n = length ctx
    let vs = applyUpTo ♯ n
    unifyStricts (hole , ty) vs

  macro
    intro→fill : Tactic
    intro→fill hole = do
      print "***********************"
      inferType hole >>= printS
      print "***********************"
      intro hole fillFromContext

    intros→fill : Tactic
    intros→fill hole = do
      print "***********************"
      inferType hole >>= printS
      print "***********************"
      intros hole fillFromContext

  _ : ℕ → ℕ
  _ = intro→fill

  _ : ∀ (n : ℕ) → ℕ
  _ = intro→fill

  _ : ∀ {n : ℕ} → ℕ
  _ = intro→fill

  _ : ∀ ⦃ n : ℕ ⦄ → ℕ
  _ = intro→fill

  _ : Bool → Bool
  _ = intro→fill

  _ : ∀ (n : Bool) → Bool
  _ = intro→fill

  _ : ∀ {n : Bool} → Bool
  _ = intro→fill

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
