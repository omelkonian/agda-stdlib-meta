{-# OPTIONS --safe --without-K #-}

----------------------------------------------------------------------
-- Anti-Unification
--
-- This is a modified version of anti-unification as implemented by
-- the Agda stdlib.
----------------------------------------------------------------------

module Reflection.AntiUnification where

open import MetaPrelude
open import Meta

import Data.Maybe as Maybe
import Data.Nat as Nat
open import Data.Product

open import Reflection.AlphaEquality

open import Class.DecEq

----------------------------------------------------------------------
-- Utilities
----------------------------------------------------------------------

module VarDescend (♯vars : ℕ) where
  -- Descend past a variable.
  varDescend : ℕ → ℕ → ℕ
  varDescend ϕ x = if ϕ Nat.≤ᵇ x then ♯vars + x else x

  -- Descend a variable underneath pattern variables.
  patternDescend : ℕ → Pattern → Pattern × ℕ
  patternsDescend : ℕ → Args Pattern → Args Pattern × ℕ

  patternDescend ϕ (con c ps) = map₁ (con c) (patternsDescend ϕ ps)
  patternDescend ϕ (dot t)    = dot t , ϕ
  patternDescend ϕ (var x)    = var (varDescend ϕ x) , suc ϕ
  patternDescend ϕ (lit l)    = lit l , ϕ
  patternDescend ϕ (proj f)   = proj f , ϕ
  patternDescend ϕ (absurd x) = absurd (varDescend ϕ x) , suc ϕ

  patternsDescend ϕ ((arg i p) ∷ ps) =
    let (p' , ϕ') = patternDescend ϕ p
        (ps' , ϕ'') = patternsDescend ϕ' ps
    in (arg i p ∷ ps' , ϕ'')
  patternsDescend ϕ []       =
    [] , ϕ

----------------------------------------------------------------------
-- Anti-Unification
----------------------------------------------------------------------

-- `cmp` compares two different terms and assigns them a variable
-- `♯vars` is the successor of the maximum value that `cmp` should take
module AntiUnification (cmp : Term → Term → ℕ) (♯vars : ℕ) where
  open VarDescend ♯vars

  antiUnify        : ℕ → Term → Term → Term
  antiUnifyArgs    : ℕ → Args Term → Args Term → Maybe (Args Term)
  antiUnifyClauses : ℕ → Clauses → Clauses → Maybe Clauses
  antiUnifyClause  : ℕ → Clause → Clause → Maybe Clause

  antiUnify ϕ t@(var x args) t'@(var y args') with x ≡ᵇ y | antiUnifyArgs ϕ args args'
  ... | _     | nothing    = var (cmp t t' + ϕ) []
  ... | false | just uargs = var (cmp t t' + ϕ) uargs
  ... | true  | just uargs = var (varDescend ϕ x) uargs
  antiUnify ϕ t@(con c args) t'@(con c' args') with c ≡ᵇ c' | antiUnifyArgs ϕ args args'
  ... | _     | nothing    = var (cmp t t' + ϕ) []
  ... | false | just uargs = var (cmp t t' + ϕ) []
  ... | true  | just uargs = con c uargs
  antiUnify ϕ t@(def f args) t'@(def f' args') with f ≡ᵇ f' | antiUnifyArgs ϕ args args'
  ... | _     | nothing    = var (cmp t t' + ϕ) []
  ... | false | just uargs = var (cmp t t' + ϕ) []
  ... | true  | just uargs = def f uargs
  antiUnify ϕ (lam v (abs s t)) (lam _ (abs _ t')) =
    lam v (abs s (antiUnify (suc ϕ) t t'))
  antiUnify ϕ t@(pat-lam cs args) t'@(pat-lam cs' args') with antiUnifyClauses ϕ cs cs' | antiUnifyArgs ϕ args args'
  ... | nothing  | _       = var (cmp t t' + ϕ) []
  ... | _        | nothing = var (cmp t t' + ϕ) []
  ... | just ucs | just uargs = pat-lam ucs uargs
  antiUnify ϕ (Π[ s ∶ arg i a ] b) (Π[ _ ∶ arg _ a' ] b') =
    Π[ s ∶ arg i (antiUnify ϕ a a') ] antiUnify (suc ϕ) b b'
  antiUnify ϕ (sort (set t)) (sort (set t')) =
    sort (set (antiUnify ϕ t t'))
  antiUnify ϕ t@(sort (lit n)) t'@(sort (lit n')) with n ≡ᵇ n'
  ... | true  = sort (lit n)
  ... | false = var (cmp t t' + ϕ) []
  antiUnify ϕ t@(sort (propLit n)) t'@(sort (propLit n')) with n ≡ᵇ n'
  ... | true  = sort (propLit n)
  ... | false = var (cmp t t' + ϕ) []
  antiUnify ϕ t@(sort (inf n)) t'@(sort (inf n')) with n ≡ᵇ n'
  ... | true  = sort (inf n)
  ... | false = var (cmp t t' + ϕ) []
  antiUnify ϕ (sort unknown) (sort unknown) =
    sort unknown
  antiUnify ϕ t@(lit l) t'@(lit l') with l == l'
  ... | true  = lit l
  ... | false = var (cmp t t' + ϕ) []
  antiUnify ϕ t@(meta x args) t'@(meta x' args') with x == x' | antiUnifyArgs ϕ args args'
  ... | _     | nothing    = var (cmp t t' + ϕ) []
  ... | false | _          = var (cmp t t' + ϕ) []
  ... | true  | just uargs = meta x uargs
  antiUnify ϕ unknown unknown = unknown
  antiUnify ϕ t@_ t'@_ = var (cmp t t' + ϕ) []

  antiUnifyArgs ϕ (arg i t ∷ args) (arg _ t' ∷ args') =
    Maybe.map (arg i (antiUnify ϕ t t') ∷_) (antiUnifyArgs ϕ args args')
  antiUnifyArgs ϕ [] [] = just []
  antiUnifyArgs ϕ _  _  = nothing

  antiUnifyClause ϕ (clause Γ pats t) (clause Δ pats' t') =
    Maybe.when ((Γ =α= Δ) ∧ (pats =α= pats'))
      let (upats , ϕ') = patternsDescend ϕ pats
      in clause Γ upats (antiUnify ϕ' t t')
  antiUnifyClause ϕ (absurd-clause Γ pats) (absurd-clause Δ pats') =
    Maybe.when ((Γ =α= Δ) ∧ (pats =α= pats')) $
      absurd-clause Γ pats
  antiUnifyClause ϕ _ _ =
    nothing

  antiUnifyClauses ϕ (c ∷ cs) (c' ∷ cs') =
    Maybe.ap (Maybe.map _∷_ (antiUnifyClause ϕ c c')) (antiUnifyClauses ϕ cs cs')
  antiUnifyClauses ϕ _ _ =
    just []
