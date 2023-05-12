{-# OPTIONS --safe --without-K #-}
module Reflection.Utils.TCI where

open import Prelude
open import Meta

import Data.Sum
open import Data.List using (map; zipWith)
open import Reflection.Utils
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Class.DecEq

open import Class.Functor
open import Class.Monad
open import Class.MonadError.Instances
open import Class.MonadReader.Instances
open import Class.MonadTC.Instances
open import Class.Traversable

private
  variable a b c : Level
           A : Set a
           B : Set b

module _ {M : ∀ {a} → Set a → Set a} ⦃ _ : Monad M ⦄ ⦃ me : MonadError (List ErrorPart) M ⦄
         ⦃ mre : MonadReader TCEnv M ⦄ ⦃ _ : MonadTC M ⦄ where

  instance _ = Functor-M

  logTelescope : List (Maybe String × Arg Type) → M ⊤
  logTelescope l = withAppendDebugPath "context" do
    catch (helper (length l) l) (λ _ → debugLog1 "Error while printing the context!")
    where
      helper : ℕ → List (Maybe String × Arg Type) → M ⊤
      helper n [] = return _
      helper n ((x , ty@(arg _ t)) ∷ l) = do
        let name = case x of λ where
          nothing   → "?"
          (just "") → "_"
          (just x)  → x
        debugLog ("  " ∷ᵈ name ∷ᵈ " : "  ∷ᵈ mapVars (_∸ (n ∸ (1 + length l))) t ∷ᵈ [])
        extendContext (name , ty) $ helper n l

  logContext : Telescope → M ⊤
  logContext l = withAppendDebugPath "context" do
    debugLog1 "Context:"
    catch (helper (length l) l) (λ _ → debugLog1 "Error while printing the context!")
    catch (do
      goalTy ← goalTy
      debugLog ("  ⊢ " ∷ᵈ goalTy ∷ᵈ []))
      λ _ → do
        inj₁ t ← reader TCEnv.goal
          where _ → error1 "Bug in logContext!"
        debugLog ("Error while infering the goal type! Goal: " ∷ᵈ t ∷ᵈ [])
    where
      helper : ℕ → Telescope → M ⊤
      helper n [] = return _
      helper n ((_ , arg _ t) ∷ l) = do
        helper n l
        debugLog ("  " ∷ᵈ ♯ (n ∸ (length l + 1)) ∷ᵈ " : " ∷ᵈ mapVars (_+ (n ∸ length l)) t ∷ᵈ [])

  logCurrentContext : M ⊤
  logCurrentContext = markDontFail "logCurrentContext" (logContext =<< getContext)

  inDebugPath : String → M A → M A
  inDebugPath path x = withAppendDebugPath path do
    debugLog (("*****" <+> path <+> "*****") ∷ᵈ [])
    logCurrentContext
    x

  viewAndReduceTy : Type → M TypeView
  viewAndReduceTy ty = helper ty =<< (length ∘ proj₁ ∘ viewTy) <$> normalise ty
    where
      helper : Type → ℕ → M TypeView
      helper ty    zero = return $ viewTy ty
      helper ty (suc k) with viewTy ty
      ... | (tel , ty') = extendContext' (map (λ where (abs s t) → s , t) tel) $ do
        rTy ← reduce ty'
        (tel' , rTy') ← helper rTy k
        return (tel ++ tel' , rTy')

  getType' : Name → M TypeView
  getType' n = viewAndReduceTy =<< getType n

  getDataDef : Name → M DataDef
  getDataDef n = inDebugPath "getDataDef" do
    debugLog ("Find details for datatype: " ∷ᵈ n ∷ᵈ [])
    (data-type pars cs) ← getDefinition n
      where _ → error1 "Not a data definition!"
    debugLogᵐ ("Constructor names: " ∷ᵈᵐ cs ᵛ ∷ᵈᵐ []ᵐ)
    cs' ← traverse (λ n → (n ,_) <$> getType' n) cs
    debugLogᵐ ("Result: " ∷ᵈᵐ cs' ᵛⁿ ∷ᵈᵐ []ᵐ)
    args ← proj₁ <$> getType' n
    return record { name = n ; constructors = cs' ; params = take pars args ; indices = drop pars args }

  getRecordDef : Name → M RecordDef
  getRecordDef n = do
    (record-type c fs) ← getDefinition n
      where _ → error1 "Not a record definition!"
    args ← proj₁ <$> getType' n
    return (record { name = c ; fields = fs ; params = args })

  getDataOrRecordDef : Name → M (DataDef ⊎ RecordDef)
  getDataOrRecordDef n =
    catch (inj₁ <$> getDataDef n)
      λ _ → catch (inj₂ <$> getRecordDef n)
      λ _ → error1 "Neither a data not a record definition!"

  getParams : Name → M (List (Abs (Arg Type)))
  getParams n = Data.Sum.[ DataDef.params , RecordDef.params ] <$> getDataOrRecordDef n

  getParamsAndIndices : Name → M (List (Abs (Arg Type)))
  getParamsAndIndices n =
    Data.Sum.[ (λ d → DataDef.params d ++ DataDef.indices d) , RecordDef.params ] <$> getDataOrRecordDef n

  getFuel : String → M ℕ
  getFuel s = do
    fuels ← reader (λ where record { options = record { fuel = f } } → f )
    case lookupᵇ (λ s s' → ⌊ s ≟ s' ⌋) fuels s of λ where
      nothing  → error1 ("Key" <+> s <+> "doesn't exist in the fuels map")
      (just f) → return f

  isSort : Term → M Bool
  isSort t = do
    (agda-sort _) ← normalise t
      where _ → return false
    return true

  isNArySort : ℕ → Term → M Bool
  isNArySort n t = do
    (tel , ty) ← viewAndReduceTy t
    b ← isSort ty
    return (⌊ (length tel) ≟ n ⌋ ∧ b)

  isDefT : Name → Term → M Bool
  isDefT n t = do
    (def n' _) ← normalise t
      where _ → return false
    return ⌊ n ≟ n' ⌋

  -- run a computation that returns a term, resetting the TC state but
  -- ensuring that the term doesn't contain any metavariables
  withSafeReset : M Term → M Term
  withSafeReset x = runAndReset $ do
    t ← x
    let m = findMetas t
    if null m
      then return t
      else do
        debugLogᵐ ("Remaining metavariables:" ∷ᵈᵐ m ᵛⁿ ∷ᵈᵐ []ᵐ)
        debugLog ("In term: " ∷ᵈ t ∷ᵈ [])
        error1 "Unsolved metavariables remaining in withSafeReset!"

  -- apply a list of terms to a name, picking the correct constructor & visibility
  applyWithVisibility : Name → List Term → M Term
  applyWithVisibility n l = do
    (argTys , _) ← getType' n
    nameConstr n (zipWith (λ where (abs _ (arg i _)) → arg i) argTys l)
