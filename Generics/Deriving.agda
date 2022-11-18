{-# OPTIONS --safe --without-K #-}
module Generics.Deriving where

open import Agda.Primitive
open import Data.Unit
open import Data.List
open import Data.Product
open import Reflection

open import Class.Functor.Core
open import Generics.Core

Derivation = List ( Name -- name of the type to derive an instance for
                  × Name -- identifier of the function/instance to generate
                  )
           → TC ⊤ -- computed instance to unquote

record Derivable (F : Type↑) : Set where
  field DERIVE' : Derivation
open Derivable ⦃...⦄ public

DERIVE : ∀ (F : Type↑) → ⦃ Derivable F ⦄ → Derivation
DERIVE F = DERIVE' {F = F}

record Derivable¹ (F : Type↑ → Setω) : Setω where
  field DERIVE¹' : Derivation
open Derivable¹ ⦃...⦄ public

DERIVE¹ : ∀ (F : Type↑ → Setω) → ⦃ Derivable¹ F ⦄ → Derivation
DERIVE¹ F = DERIVE¹' {F = F}

record Derivableω (F : Setω) : Setω where
  field DERIVEω' : Derivation
open Derivableω ⦃...⦄ public

DERIVEω : ∀ (F : Setω) → ⦃ Derivableω F ⦄ → Derivation
DERIVEω F = DERIVEω' {F = F}
