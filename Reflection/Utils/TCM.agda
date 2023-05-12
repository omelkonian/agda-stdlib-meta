{-# OPTIONS --safe --without-K #-}
module Reflection.Utils.TCM where

open import Prelude

import Data.List.NonEmpty as NE
open import Data.List
open import Data.String as Str hiding (length)
open import Reflection hiding (visibility)
open import Reflection.Syntax
open import Reflection.TypeChecking.Monad.Syntax
open import Reflection.Utils
open import Reflection.Utils.Debug

private variable
  ℓ : Level
  A B : Set ℓ

fresh-level : TC Level
fresh-level = newMeta (quote Level ∙) >>= unquoteTC

withHole : Type → (Hole → TC ⊤) → TC Hole
withHole ty k = do
  hole′ ← newMeta ty
  k hole′
  return hole′

apply : Type → Term → List (Arg Term) → TC (Type × Term)
apply A t []       = return (A , t)
apply A t (a ∷ as) = do
  A ← reduce A
  A , t ← apply₁ A t a
  apply A t as
  where
    apply₁ : Type → Term → Arg Term → TC (Type × Term)
    apply₁ (pi (arg i₁@(arg-info k _) A) B) t₁ (arg i₂ t₂) = do
      a ← fresh-level
      b ← fresh-level
      A ← unquoteTC {A = Set a} A
      B ← unquoteTC {A = A → Set b} (lam visible B)
      t₂ ← unquoteTC {A = A} t₂
      Bt₂ ← quoteTC (B t₂)
      case k of λ where
        visible → do
          t₁ ← unquoteTC {A = ∀ (x : A) → B x} t₁
          Bt₂ ,_ <$> quoteTC (t₁ t₂)
        hidden → do
          t₁ ← unquoteTC {A = ∀ {x : A} → B x} t₁
          Bt₂ ,_ <$> quoteTC (t₁ {x = t₂})
        instance′ → do
          t₁ ← unquoteTC {A = ∀ ⦃ x : A ⦄ → B x} t₁
          Bt₂ ,_ <$> quoteTC (t₁ ⦃ x = t₂ ⦄)
    apply₁ (meta x _) _ _ = blockOnMeta x
    apply₁ A          _ _ = error "apply: not a Π-type"

_-∙-_ : Term → Term → TC Term
f -∙- x = do
  ty ← inferType f
  proj₂ <$> apply ty f [ vArg x ]

_-∗-_ : Term → List Term → TC Term
f -∗- []       = return f
f -∗- (x ∷ xs) = f -∙- x >>= _-∗- xs

instantiate : Hole → TC Term
instantiate = (_>>= normalise) ∘ reduce

module _ where -- ** unification
  open Debug ("Generics.unifyStrict", 100)

  ensureNoMetas : Term → TC ⊤
  ensureNoMetas = λ where
    (var x args) → noMetaArgs args
    (con c args) → noMetaArgs args
    (def f args) → noMetaArgs args
    (lam v (abs _ t)) → ensureNoMetas t
    (pat-lam cs args) → noMetaClauses cs >> noMetaArgs args
    (pi a b) → noMetaArg a >> noMetaAbs b
    (agda-sort s) → noMetaSort s
    (lit l) → pure _
    -- (meta x _) → errorP "meta found!"
    (meta x _) → blockOnMeta x
    unknown → pure _
     where
      noMetaArg : Arg Term → TC ⊤
      noMetaArg (arg _ v) = ensureNoMetas v

      noMetaArgs : List (Arg Term) → TC ⊤
      noMetaArgs [] = pure _
      noMetaArgs (v ∷ vs) = noMetaArg v >> noMetaArgs vs

      noMetaClause : Clause → TC ⊤
      noMetaClause (clause _ ps t) = ensureNoMetas t
      noMetaClause (absurd-clause _ ps) = pure _

      noMetaClauses : List Clause → TC ⊤
      noMetaClauses [] = pure _
      noMetaClauses (c ∷ cs) = noMetaClause c >> noMetaClauses cs

      noMetaAbs : Abs Term → TC ⊤
      noMetaAbs (abs _ v) = ensureNoMetas v

      noMetaSort : Sort → TC ⊤
      noMetaSort (set t) = ensureNoMetas t
      noMetaSort _       = pure _

  module NewMeta where
    unifyStrict : THole → Term → TC ⊤
    unifyStrict (hole , ty) x = do
      printLn $ showTerm hole Str.++ " :=? " Str.++ showTerm x
      m ← newMeta ty
      noConstraints $
        unify m x >> unify hole m
      printLn $ showTerm hole Str.++ " := " Str.++ showTerm x

  module NoMeta where
    unifyStrict : THole → Term → TC ⊤
    unifyStrict (hole , ty) x = do
      -- unify hole x
      -- instantiate hole >>= ensureNoMetas

      print "———————————————————————————————————————"
      printTerm "x" x
      unify hole x
      hole ← normalise hole
      printTerm "hole′" hole
      -- (x ∷ hole ∷ []) ← mapM instantiate (x ∷ hole ∷ [])
      --   where _ → _IMPOSSIBLE_
      -- printTerm "x′" x
      ensureNoMetas hole
      printLn "No metas found :)"

  open NewMeta public
  -- open NoMeta public

  unifyStricts : THole → List Term → TC ⊤
  unifyStricts ht = NE.foldl₁ _<|>_
                  ∘ (NE._∷ʳ error "∅")
                  ∘ map ({-noConstraints ∘ -}unifyStrict ht)

compatible? : Type → Type → TC Bool
compatible? ty ty′ = do
  -- print $ show ty ◇ " ≈? " ◇ show ty′
  b ← runSpeculative $ (_, false) <$>
    catchTC (unify (varsToUnknown ty) (varsToUnknown ty′) >> return true)
            (return false)
  -- print $ "  ——→ " ◇ show b
  return b
