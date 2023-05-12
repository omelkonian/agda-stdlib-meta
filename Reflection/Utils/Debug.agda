-------------------------------------------------
-- ** Errors, debugging

{-# OPTIONS --safe --without-K #-}
module Reflection.Utils.Debug where

open import Level using (Level)
open import Function using (_∘_; _$_)

open import Data.Unit using (⊤)
open import Data.String as Str using (String)
open import Data.List using ([]; _∷_; [_]; length; List; allFin; zip)
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)

open import Reflection hiding (_>>_; _>>=_)
open import Reflection.Term
open import Reflection.Meta

open import Class.Show.Core
open import Class.Show.Instances
open import Class.Functor
open import Class.Monad
open import Class.Traversable.Core
open import Class.Traversable.Instances

private variable
  ℓ : Level
  A : Set ℓ

error : String → TC A
error s = typeError [ strErr s ]

_IMPOSSIBLE_ : TC A
_IMPOSSIBLE_ = error "IMPOSSIBLE"

enumerate : (xs : List A) → List (Fin (length xs) × A)
enumerate xs = zip (allFin $ length xs) xs

module Debug (v : String × ℕ) where
  -- i.e. set {-# OPTIONS -v v₁:v₂ #-} to enable such messages in the **debug** buffer.

  print printLn : String → TC ⊤
  print s = debugPrint (v .proj₁) (v .proj₂) [ strErr s ]
  printLn = print ∘ (Str._++ "\n")
  printLns = print ∘ Str.unlines

  printS : ⦃ _ : Show A ⦄ → A → TC ⊤
  printS = print ∘ show

  errorP : String → TC A
  errorP s = printLn s >> error s

  printTerm : String → Term → TC ⊤
  printTerm s t = do
    ty ← inferType t
    printLns
      ( (s Str.++ ": {")
      ∷ showTerm ty
      ∷ " ∋ "
      ∷ showTerm t
      ∷ "}\n"
      ∷ [])

  printContext : Telescope → TC ⊤
  printContext ctx = do
    print "\t----CTX----"
    void $ traverse go (enumerate ctx)
    where
      go : Fin (length ctx) × String × Arg Type → TC ⊤
      go (i , s , ty) = print $
        "\t#" Str.++ show i Str.++ " " Str.++ s Str.++ " : " Str.++ show ty

  printCurrentContext : TC ⊤
  printCurrentContext = printContext =<< getContext

  -- ** definitions
  genSimpleDef : Name → Type → Term → TC ⊤
  genSimpleDef n ty e = do
    print "Generaring..."
    declareDef (vArg n) ty
    print $ "```\n" Str.++ showName n Str.++ " : "
     Str.++ " " Str.++ showTerm ty
    defineFun n [ clause [] [] e ]
    print $ showName n Str.++ " = " Str.++ " "
     Str.++ showTerm e Str.++ "\n```"

module DebugI (v : String) where
  -- i.e. set {-# OPTIONS -v ⟨v⟩:0 #-} to enable messages in the **info** buffer.
  open Debug (v , 0) public

-- set {-# OPTIONS -v trace:100 #-} when tracing
macro
  trace : ∀ {A : Set} ⦃ _ : Show A ⦄ → A → Term → Term → TC ⊤
  trace x t hole = print ("trace: " Str.++ show x) >> unify hole t
    where open Debug ("trace" , 100)
