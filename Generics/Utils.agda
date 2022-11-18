{-# OPTIONS --safe --without-K #-}
module Generics.Utils where

open import Level using (Level)
open import Function

open import Reflection hiding (visibility)
open import Reflection.Term
import Reflection.Abstraction as Abs
open import Reflection.Argument as Arg hiding (map)
import Reflection.Name as Name
open import Reflection.Pattern
open import Reflection.Argument.Information
open import Reflection.Argument.Visibility as Vis
open import Reflection.TypeChecking.Monad.Syntax

open import Data.Unit
open import Data.Product hiding (map; zip)
open import Data.List
import Data.List.NonEmpty as NE
open import Data.Nat
open import Data.Bool
open import Data.Maybe hiding (map; zip; _>>=_)
open import Data.Fin hiding (_+_)
open import Data.String as Str hiding (length)

open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Generics.Core
open import Generics.Debug

private variable
  ℓ : Level
  A B : Set ℓ

absName : Abs A → String
absName (abs s x) = s

getVisibility : ∀ {a} {A : Set a} → Arg A → Visibility
getVisibility (arg (arg-info v _) _) = v

findMetas : Term → List Term
findMetas' : List (Arg Term) → List Term
findMetasCl : List Clause → List Term

findMetas (var x args) = findMetas' args
findMetas (con c args) = findMetas' args
findMetas (def f args) = findMetas' args
findMetas (lam v (abs _ x)) = findMetas x
findMetas (pat-lam cs args) = findMetasCl cs Data.List.++ findMetas' args
findMetas (pi (arg _ a) (abs _ b)) = findMetas a Data.List.++ findMetas b
findMetas (agda-sort s) = []
findMetas (lit l) = []
findMetas m@(meta x args) = m ∷ findMetas' args
findMetas unknown = []

findMetas' [] = []
findMetas' ((arg _ t) ∷ ts) = findMetas t Data.List.++ findMetas' ts

findMetasCl [] = []
findMetasCl (Clause.clause tel ps t ∷ c) = findMetas t Data.List.++ findMetasCl c
findMetasCl (Clause.absurd-clause tel ps ∷ c) = findMetasCl c

isMeta : Term → Bool
isMeta (meta _ _) = true
isMeta _ = false

UnquoteDecl : Set
UnquoteDecl = TC ⊤

unArgs : Args A → List A
unArgs = map unArg

mapVariables : (ℕ → ℕ) → (Pattern → Pattern)
mapVariables f (Pattern.var n)      = Pattern.var (f n)
mapVariables f (Pattern.con c args) = Pattern.con c $ go args
  where
    go : List (Arg Pattern) → List (Arg Pattern)
    go [] = []
    go (arg i p ∷ l) = arg i (mapVariables f p) ∷ go l
mapVariables _ p                    = p

-- alternative view of function types as a pair of a list of arguments and a return type
TypeView = List (Abs (Arg Type)) × Type

viewTy : Type → TypeView
viewTy (Π[ s ∶ a ] ty) = map₁ ((abs s a) ∷_) (viewTy ty)
viewTy ty              = [] , ty

tyView : TypeView → Type
tyView ([] , ty) = ty
tyView (abs s a ∷ as , ty) = Π[ s ∶ a ] tyView (as , ty)

argumentWise : (Type → Type) → Type → Type
argumentWise f ty =
  let
    as , r = viewTy ty
    as′ = map (Abs.map $ Arg.map f) as
  in tyView (as′ , r)

viewTy′ : Type → Args Type × Type
viewTy′ (Π[ _ ∶ a ] ty) = map₁ (a ∷_) (viewTy′ ty)
viewTy′ ty              = [] , ty

argTys : Type → Args Type
argTys = proj₁ ∘ viewTy′

resultTy : Type → Type
resultTy = proj₂ ∘ viewTy′

tyName : Type → Maybe Name
tyName (con n _) = just n
tyName (def n _) = just n
tyName _         = nothing

args : Term → Args Term
args (var _ xs)  = xs
args (def _ xs)  = xs
args (con _ xs)  = xs
args _           = []

args′ : Term → List Term
args′ = unArgs ∘ args

module _ (f : ℕ → ℕ) where

  private
    _⁇_ : ℕ → ℕ → ℕ
    bound ⁇ x = if bound ≤ᵇ x then f x else x

  mutual
    mapFreeVars : ℕ → (Term → Term)
    mapFreeVars bound = λ where
      (var x as)
        → var (bound ⁇ x) (mapFreeVars∗ bound as)
      (def c as)
        → def c (mapFreeVars∗ bound as)
      (con c as)
        → con c (mapFreeVars∗ bound as)
      (lam v (abs x t))
        → lam v (abs x (mapFreeVars (suc bound) t))
      (pat-lam cs as)
        → pat-lam (mapFreeVarsᶜ∗ bound cs) (mapFreeVars∗ bound as)
      (pi (arg i t) (abs x t′))
        → pi (arg i (mapFreeVars bound t)) (abs x (mapFreeVars (suc bound) t′))
      (agda-sort s)
        → agda-sort (mapFreeVarsˢ bound s)
      (meta x as)
        → meta x (mapFreeVars∗ bound as)
      t → t
    mapFreeVars∗ : ℕ → (Args Term → Args Term)
    mapFreeVars∗ b = λ where
      [] → []
      (arg i t ∷ ts) → arg i (mapFreeVars b t) ∷ mapFreeVars∗ b ts

    mapFreeVarsᵖ : ℕ → (Pattern → Pattern)
    mapFreeVarsᵖ b = λ where
      (con c ps) → con c (mapFreeVarsᵖ∗ b ps)
      (dot t)    → dot (mapFreeVars b t)
      (absurd x) → absurd (b ⁇ x)
      p → p
    mapFreeVarsᵖ∗ : ℕ → (Args Pattern → Args Pattern)
    mapFreeVarsᵖ∗ b = λ where
      [] → []
      (arg i p ∷ ps) → arg i (mapFreeVarsᵖ b p) ∷ mapFreeVarsᵖ∗ (suc b) ps

    mapFreeVarsᵗ : ℕ → (Telescope → Telescope)
    mapFreeVarsᵗ b = λ where
      [] → []
      ((s , arg i t) ∷ ts) → (s , arg i (mapFreeVars b t)) ∷ mapFreeVarsᵗ (suc b) ts

    mapFreeVarsᶜ : ℕ → (Clause → Clause)
    mapFreeVarsᶜ b = λ where
      -- clause        : (tel : List (Σ String λ _ → Arg Type)) (ps : List (Arg Pattern)) (t : Term) → Clause
      (clause tel ps t) → clause (mapFreeVarsᵗ b tel) (mapFreeVarsᵖ∗ b ps) (mapFreeVars (length tel + b) t)
      -- absurd-clause : (tel : List (Σ String λ _ → Arg Type)) (ps : List (Arg Pattern)) → Clause
      (absurd-clause tel ps) → absurd-clause (mapFreeVarsᵗ b tel) (mapFreeVarsᵖ∗ b ps)
    mapFreeVarsᶜ∗ : ℕ → (List Clause → List Clause)
    mapFreeVarsᶜ∗ b = λ where
      [] → []
      (c ∷ cs) → mapFreeVarsᶜ b c ∷ mapFreeVarsᶜ∗ b cs

    mapFreeVarsˢ : ℕ → (Sort → Sort)
    mapFreeVarsˢ b = λ where
      (set t) → set (mapFreeVars b t)
      (prop t) → prop (mapFreeVars b t)
      s → s

  mapVars : Term → Term
  mapVars = mapFreeVars 0

varsToUnknown : Type → Type
varsToUnknown′ : Args Type → Args Type

varsToUnknown (var _ _)  = unknown
varsToUnknown (def c xs) = def c (varsToUnknown′ xs)
varsToUnknown (con c xs) = con c (varsToUnknown′ xs)
varsToUnknown ty         = ty

varsToUnknown′ []              = []
varsToUnknown′ (arg i ty ∷ xs) = arg i (varsToUnknown ty) ∷ varsToUnknown′ xs

parameters : Definition → ℕ
parameters (data-type pars _) = pars
parameters _                  = 0

vArgs : Args A → List A
vArgs [] = []
vArgs (vArg x ∷ xs) = x ∷ vArgs xs
vArgs (_      ∷ xs) = vArgs xs

argInfo : Arg A → ArgInfo
argInfo (arg i _) = i

isVisible? : (a : Arg A) → Dec (visibility (argInfo a) ≡ visible)
isVisible? a = visibility (argInfo a) Vis.≟ visible

isInstance? : (a : Arg A) → Dec (visibility (argInfo a) ≡ instance′)
isInstance? a = visibility (argInfo a) Vis.≟ instance′

isHidden? : (a : Arg A) → Dec (visibility (argInfo a) ≡ hidden)
isHidden? a = visibility (argInfo a) Vis.≟ hidden

remove-iArgs : Args A → Args A
remove-iArgs [] = []
remove-iArgs (iArg x ∷ xs) = remove-iArgs xs
remove-iArgs (x      ∷ xs) = x ∷ remove-iArgs xs

hide : Arg A → Arg A
hide (vArg x) = hArg x
hide (hArg x) = hArg x
hide (iArg x) = iArg x
hide a        = a

∀indices⋯ : Args Type → Type → Type
∀indices⋯ []       ty = ty
∀indices⋯ (i ∷ is) ty = Π[ "_" ∶ hide i ] (∀indices⋯ is ty)

apply⋯ : Args Type → Name → Type
apply⋯ is n = def n $ remove-iArgs (map (λ{ (n , arg i _) → arg i (♯ (length is ∸ suc (toℕ n)))}) (zip (allFin $ length is) is))

TTerm = Term × Type
Hole  = Term
THole = Hole × Type

Context = List (Arg Type)
Tactic  = Hole → TC ⊤

fresh-level : TC Level
fresh-level = newMeta (quote Level ∙) >>= unquoteTC

withHole : Type → Tactic → TC Hole
withHole ty k = do
  hole′ ← newMeta ty
  k hole′
  return hole′

-- ** records
mkRecord : List (Name × Term) → Term
mkRecord fs = pat-lam (map (λ where (fn , e) → clause [] [ vArg (proj fn) ] e) fs) []

updateField : List Name → Term → Name → Term → Term
updateField fs rexp fn fexp =
  pat-lam (flip map fs $ λ f →
    if ⌊ f Name.≟ fn ⌋ then
      clause [] [ vArg (proj fn) ] fexp
    else
      clause [] [ vArg (proj f) ] (f ∙⟦ rexp ⟧)
    ) []

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
