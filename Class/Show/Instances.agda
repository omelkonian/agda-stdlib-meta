{-# OPTIONS --safe --without-K #-}
module Class.Show.Instances where

open import Level using (Level; _⊔_)
open import Function using (id; _∋_; _$_; _∘_)
open import Data.String as Str using (String; _++_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Data.Char using (Char)
open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.Float using (Float)
open import Data.List using (List; map)
open import Data.Fin as Fin using (Fin)
open import Reflection
open import Reflection.Term
open import Reflection.Meta

open import Class.Show.Core

private variable
  ℓ ℓ′ : Level
  A : Set ℓ; B : Set ℓ′

mkShow-× : ⦃ Show A ⦄ → ⦃ Show B ⦄ → Show (A × B)
mkShow-× .show (x , y) = Str.parens $ show x ++ " , " ++ show y

Show-List : ⦃ Show A ⦄ → Show (List A)
Show-List .show = Str.braces ∘ Str.intersperse ", " ∘ map show

instance
  Show-String = mkShow id

  Show-⊤ : Show ⊤
  Show-⊤ .show tt = "tt"

  Show-Char = Show _ ∋ record {M}
    where import Data.Char as M

  Show-Bool = Show _ ∋ record {M}
    where import Data.Bool.Show as M

  Show-ℕ = Show _ ∋ record {M}
    where import Data.Nat.Show as M

  Show-Fin : ∀ {n} → Show (Fin n)
  Show-Fin .show = ("# " ++_) ∘ show ∘ Fin.toℕ

  Show-Float = Show _ ∋ record {M}
    where import Data.Float as M

  Show-Name = mkShow showName
  Show-Meta = mkShow showMeta
  Show-Relevance = mkShow showRel -- showRelevance
  Show-Vis = mkShow showVisibility
  Show-Literal = mkShow showLiteral

Show-Arg : ⦃ Show A ⦄ → Show (Arg A)
Show-Arg .show (arg (arg-info v _) x) = show v ++ show x

Show-Abs : ⦃ Show A ⦄ → Show (Abs A)
Show-Abs .show (abs s x) = "abs " ++ show s ++ " " ++ show x

instance
  Show-Names = Show (Args Term) ∋ mkShow showTerms
  Show-Term = mkShow showTerm
  Show-Sort = mkShow showSort
  Show-Patterns = Show (Args Pattern) ∋ mkShow showPatterns
  Show-Pattern = mkShow showPattern
  Show-Clause = mkShow showClause
  Show-Clauses = Show (List Clause) ∋ mkShow showClauses
  Show-Tel = Show Telescope ∋ mkShow showTel
  Show-Definition = mkShow showDefinition

  Show-AName = Show (Arg Name) ∋ Show-Arg
  Show-AType = Show (Arg Type) ∋ Show-Arg
  Show-ATerms = Show (Args Name) ∋ Show-List
