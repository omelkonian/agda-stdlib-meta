{-# OPTIONS --safe --without-K #-}

module Reflection.Syntax where

open import Prelude

open import Reflection.Argument hiding (map) public
open import Reflection.Term hiding (_≟_; getName) public
open import Reflection.Name hiding (_≟_; _≈_; _≈?_) public
open import Reflection.Definition hiding (_≟_) public
open import Reflection.Meta hiding (_≟_; _≈_; _≈?_) public
open import Reflection.Abstraction using (unAbs) public

open import Reflection.Argument.Visibility using (Visibility) public
open import Reflection.Abstraction using (unAbs) public
open import Reflection.Argument using (vArg; hArg; iArg; unArg; _⟨∷⟩_; map-Args) public
open import Reflection using (Term; Type; Name; data-cons; pi; abs; Abs; Arg; Clause; data-type; record-type; var; con; def; lam; pat-lam; arg; agda-sort; lit; meta; unknown; Pattern; strErr; ErrorPart; arg-info; visible; Definition) public

open import Generics using (absName; getVisibility; findMetas; isMeta; UnquoteDecl; Tactic) public
