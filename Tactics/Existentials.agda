module Tactics.Existentials where

open import Function
open import Data.Product using (∃; _×_; _,_; -,_; proj₁; proj₂; map₁; map₂)
open import Data.Nat as Nat using (ℕ; suc; _∸_)
open import Data.List as L using (reverse; upTo; length)
open import Data.String using (String)

open import Reflection hiding (return; _>>=_; _>>_; _≟_)
open import Reflection.Term hiding (_≟_)

open import Generics

open import Class.Functor
open import Class.Monad

mkExistential : ℕ → Name → TC Term
mkExistential lvl t = do
  ty ← getType t
  let n = length (argTys ty) ∸ lvl
  return $ go n n
  where
    go : ℕ → ℕ → Term
    go n₀ 0       = def t (fmap (λ n → vArg (♯ n)) (reverse $ upTo n₀))
    go n₀ (suc n) = quote ∃ ∙⟦ (`λ "_" ⇒ go n₀ n) ⟧

macro
  mk∃ : Name → Tactic
  mk∃ t hole = mkExistential 0 t >>= unify hole

private
  data X : ℕ → String → ℕ → Set where
    mkX : X 0 "" 1

  _ : mk∃ X
  _ = 0 , "" , 1 , mkX

  module _ (n : ℕ) where
    data Y : String → ℕ → Set where
      mkY : Y "" 1

    _ : mk∃ Y
    _ = "" , 1 , mkY

    module _ (s : String) where

      data Z : ℕ → Set where
        mkZ : Z 1

      _ : mk∃ Z
      _ = 1 , mkZ

    _ : mk∃ Z
    _ = "sth" , 1 , mkZ

  _ : mk∃ Y
  _ = 42 , "" , 1 , mkY

  _ : mk∃ Z
  _ = 0 , "sth" , 1 , mkZ
