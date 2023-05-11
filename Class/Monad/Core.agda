{-# OPTIONS --safe --without-K #-}

module Class.Monad.Core where

open import Prelude

open import Class.Functor

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

record Monad (M : ∀ {a} → Set a → Set a) : Setω where
  infixl 1 _>>=_ _>>_ _>=>_
  infixr 1 _=<<_ _<=<_

  field
    return : A → M A
    _>>=_  : M A → (A → M B) → M B

  _>>_ : M A → M B → M B
  m₁ >> m₂ = m₁ >>= λ _ → m₂

  _=<<_ : (A → M B) → M A → M B
  f =<< c = c >>= f

  _>=>_ : (A → M B) → (B → M C) → (A → M C)
  f >=> g = _=<<_ g ∘ f

  _<=<_ : (B → M C) → (A → M B) → (A → M C)
  g <=< f = f >=> g

  join : M (M A) → M A
  join m = m >>= id

  Functor-M : Functor M
  Functor-M = λ where ._<$>_ f x → return ∘ f =<< x

  instance _ = Functor-M

  mapM : (A → M B) → List A → M (List B)
  mapM f []       = return []
  mapM f (x ∷ xs) = do y ← f x; y ∷_ <$> mapM f xs

  concatMapM : (A → M (List B)) → List A → M (List B)
  concatMapM f xs = concat <$> mapM f xs

  forM : List A → (A → M B) → M (List B)
  forM []       _ = return []
  forM (x ∷ xs) f = do y ← f x; y ∷_ <$> forM xs f

  -- concatForM : List A → (A → M (List B)) → M (List B)
  -- concatForM xs f = concat <$> forM xs f

  return⊤ void : M A → M ⊤
  return⊤ k = k >> return tt
  void = return⊤

  filterM : (A → M Bool) → List A → M (List A)
  filterM _ [] = return []
  filterM p (x ∷ xs) = do
    b ← p x
    ((if b then [ x ] else []) ++_) <$> filterM p xs

  -- traverse : ∀ {A B : Type} {M : Type → Type} → ⦃ Applicative M ⦄ → ⦃ Monad M ⦄ → (A → M B) → List A → M (List B)
  -- traverse f = λ where
  --   [] → return []
  --   (x ∷ xs) → ⦇ f x ∷ traverse f xs ⦈

  -- do-pure : ∀ {A : Type ℓ} {x : A} {mx : Maybe A} {f : A → Bool}
  --   → mx ≡ just x
  --   → f x ≡ true
  --   → fromMaybe false (mx >>= pure ∘ f) ≡ true
  -- do-pure refl f≡ rewrit
open Monad ⦃...⦄ public
