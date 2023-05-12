{-# OPTIONS -v eta:100 #-}
module Tactics.Eta where

open import Prelude

open import Data.List
open import Data.Fin

open import Class.Monad
open import Class.Semigroup
open import Class.Show
open import Reflection hiding (return; _>>=_; _>>_)
open import Reflection.Syntax hiding (toℕ)
open import Reflection.Utils
open import Reflection.Utils.Debug

open Debug ("eta" , 100)

saturate : Term → Args Type → TC Term
saturate f as = case f of λ where
  (def c as′) → return $ def c (as′ ++ as)
  _           → error $ "cannot saturate arbitrary expressions, only definitions"

macro
  η : Term → Hole → TC ⊤
  η f hole = do
    print "*****************************"
    print $ "f: " ◇ show f
    ty ← inferType f -- =<< reduce f
    print $ "ty: " ◇ show ty
    let as , _ = viewTy′ ty
    print $ "as: " ◇ show as
    f′ ← saturate f $ flip map (enumerate as) $ λ where
      (n , arg i _) → arg i (♯ (length as ∸ suc (toℕ n)))
    print $ "f′: " ◇ show f′
    unify hole $ foldr (λ x t → Π[ "_" ∶ x ] t) f′ as

private
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
