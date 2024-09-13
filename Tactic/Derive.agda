-- Generic type class dervations. Works with mutually recursive types
-- and can use mutual recursion to satisfy the termination
-- checker. Writing an actual derivation strategy then does not
-- require dealing with any mutual recursion, it is all handled here.
--
-- TODO: This breaks with:
-- - mutual recursion that nests too deep (i.e. deeper than 1, e.g. Term)
-- - indexed datatypes that require absurd clauses (e.g. Vec)
--
-- TODO: support type classes with more than one field
--
-- TODO: enable using existing code for instance when mutually recursing
--
-- TODO: Requires K to pass the termination checker. Maybe we can do without somehow.

{-# OPTIONS -v allTactics:100 #-}
{-# OPTIONS --safe --without-K #-}
open import Meta.Init

module Tactic.Derive (className : Name) (projName : Name) where

open import Meta.Prelude

open import Agda.Builtin.Reflection using () renaming (primShowQName to showName)

import Data.List as L
import Data.List.NonEmpty as NE
import Data.String as S
open import Data.Maybe using (fromMaybe)
open import Reflection.Tactic
open import Reflection.Utils
open import Reflection.Utils.TCI
open import Relation.Nullary.Decidable
open import Tactic.ClauseBuilder

open import Class.DecEq
open import Class.Monad
open import Class.Traversable
open import Class.Functor
open import Class.MonadReader.Instances
open import Class.MonadTC.Instances

instance
  _ = ContextMonad-MonadTC
  _ = Functor-M

open ClauseExprM

genClassType : ℕ → Name → Maybe Name → TC Type
genClassType arity dName wName = do
  params ← getParamsAndIndices dName
  adjParams ← adjustParams $ take (length params ∸ arity) params
  debugLog1 "AdjustedParams: "
  logTelescope (L.map ((λ where (abs s x) → just s , x) ∘ proj₁) adjParams)
  ty ← applyWithVisibility dName (L.map ♯ (trueIndices adjParams))
  return $ modifyClassType wName (L.map proj₁ adjParams , ty)
  where
    adjustParams : List (Abs (Arg Type)) → TC (List ((Abs (Arg Type)) × Bool))
    adjustParams [] = return []
    adjustParams (abs x (arg _ t) ∷ l) = do
      a ← (if_then [ (abs "_" (iArg (className ∙⟦ ♯ 0 ⟧)) , false) ] else []) <$> isNArySort arity t
      ps ← extendContext (x , hArg t) (adjustParams l)
      let ps' = flip L.map ps λ where
        (abs s (arg i t) , b) → (abs s (arg i (mapVars (_+ (if b then length a else 0)) t)) , b)
      return (((abs x (hArg t) , true) ∷ a) ++ ps')

    trueIndices : {A : Set} → List (A × Bool) → List ℕ
    trueIndices [] = []
    trueIndices (x ∷ l) = if proj₂ x then length l ∷ trueIndices l else trueIndices l

    modifyClassType : Maybe Name → TypeView → Type
    modifyClassType nothing  (tel , ty) = tyView (tel , className ∙⟦ ty ⟧)
    modifyClassType (just n) (tel , ty) = tyView (tel , className ∙⟦ n ∙⟦ ty ⟧ ⟧)

lookupName : List (Name × Name) → Name → Maybe Name
lookupName = lookupᵇ (λ n n' → ⌊ n ≟ n' ⌋)

-- Look at the constructors of the argument and return all types that
-- recursively contain it. This isn't very clever right now.
genMutualHelpers : Name → TC (List Name)
genMutualHelpers n = do
  tys ← L.map (unArg ∘ unAbs) <$> (L.concatMap (proj₁ ∘ viewTy ∘ proj₂) <$> getConstrs n)
  return $ deduplicate _≟_ $ L.mapMaybe helper tys
  where
    helper : Type → Maybe Name
    helper (def n' args) =
      if L.any (λ where (arg _ (def n'' _)) → ⌊ n ≟ n'' ⌋ ; _ → false) args
      then just n' else nothing
    helper _ = nothing

module _ (arity : ℕ) (genCe : (Name → Maybe Name) → List SinglePattern → List (NE.List⁺ SinglePattern × TC (ClauseExpr ⊎ Maybe Term))) where
  -- Generate the declaration & definition of a particular derivation.
  --
  -- Takes a dictionary (for mutual recursion), a wrapper (also for
  -- mutual recursion), the name of the original type we want to derive
  -- Show for and the name we want to define Show originally at.
  deriveSingle : List (Name × Name) → Name → Name → Maybe Name → TC (Arg Name × Type × List Clause)
  deriveSingle transName dName iName wName = inDebugPath "DeriveSingle" do
    debugLog ("For: " ∷ᵈ dName ∷ᵈ [])
    goalTy ← genClassType arity dName wName
    ps ← constructorPatterns' (fromMaybe dName wName ∙)
    -- TODO: find a good way of printing this
    --debugLogᵐ ("Constrs: " ∷ᵈᵐ ps ᵛⁿ ∷ᵈᵐ []ᵐ)
    cs ← local (λ c → record c { goal = inj₂ goalTy }) $
      singleMatchExpr ([] , iArg (Pattern.proj projName)) $ contMatch $ multiMatchExprM $
        genCe (lookupName transName) ps
    let defName = maybe (maybe vArg (iArg iName) ∘ lookupName transName) (iArg iName) wName
    return (defName , goalTy , clauseExprToClauses cs)

  deriveMulti : Name × Name × List Name → TC (List (Arg Name × Type × List Clause))
  deriveMulti (dName , iName , hClasses) = do
    hClassNames ← traverse ⦃ Functor-List ⦄
      (λ cn → freshName (showName className S.++ "-" S.++ showName cn S.++ showName dName)) hClasses
    traverse ⦃ Functor-List ⦄ (deriveSingle (L.zip hClasses hClassNames) dName iName) (nothing ∷ L.map just hClasses)

  derive-Class : ⦃ TCOptions ⦄ → List (Name × Name) → UnquoteDecl
  derive-Class l = initUnquoteWithGoal (className ∙) $
    declareAndDefineFuns =<< concat <$> traverse ⦃ Functor-List ⦄ helper l
    where
      helper : Name × Name → TC (List (Arg Name × Type × List Clause))
      helper (a , b) = do hs ← genMutualHelpers a ; deriveMulti (a , b , hs)
