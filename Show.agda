{-# OPTIONS --safe --without-K #-}
module Class.Show.Core where

open import Level using (Level; _⊔_)
open import Function using (_∋_; _$_; _∘_)
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
open import Reflection.Meta

record Show {ℓ} (A : Set ℓ) : Set ℓ where
  constructor mkShow
  field show : A → String
open Show ⦃...⦄ public

Show-× : ⦃ Show A ⦄ → ⦃ Show B ⦄ → Show (A × B)
Show-× .show (x , y) = Str.parens $ show x ++ " , " ++ show y

Show-List : ⦃ Show A ⦄ → Show (List A)
Show-List .show = Str.braces ∘ Str.intersperse ", " ∘ map show

Show-Arg : ⦃ Show A ⦄ → Show (Arg A)
Show-Arg .show (arg (arg-info v _) x) = show v ++ show x

Show-Abs : ⦃ Show A ⦄ → Show (Abs A)
Show-Abs .show (abs s x) = "abs " ++ show s ++ " " ++ show x

instance
  Show-String : Show String
  Show-String .show x = x

  Show-⊤ : Show ⊤
  Show-⊤ .show tt = "tt"

  Show-Char : Show Char
  Show-Char = record {M}
    where import Data.Char as M

  Show-Bool : Show Bool
  Show-Bool = record {M}
    where import Data.Bool.Show as M

  Show-ℕ : Show ℕ
  Show-ℕ = record {M}
    where import Data.Nat.Show as M

  Show-Fin : ∀ {n} → Show (Fin n)
  Show-Fin .show = ("# " ++_) ∘ show ∘ Fin.toℕ

  Show-Float : Show Float
  Show-Float = record {M}
    where import Data.Float as M

  Show-Name = mkShow showName
  Show-Meta = mkShow showMeta
  Show-Relevance = mkShow showRel -- showRelevance
  Show-Vis = mkShow showVisibility
  Show-Literal = mkShow showLiteral

  Show-Terms = Show (List $ Arg Term) ∋ mkShow showTerms
  Show-Term = mkShow showTerm
  Show-Sort = mkShow showSort
  Show-Patterns = Show (List $ Arg Pattern) ∋ mkShow showPatterns
  Show-Pattern = mkShow showPattern
  Show-Clause = mkShow showClause
  Show-Clauses = Show (List Clause) ∋ mkShow showClauses
  Show-Tel = Show (List $ String × Arg Type) ∋ mkShow showTel
  Show-Definition = mkShow showDefinition
