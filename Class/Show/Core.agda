{-# OPTIONS --safe --without-K #-}
module Class.Show.Core where

open import Data.String using (String)

record Show {ℓ} (A : Set ℓ) : Set ℓ where
  constructor mkShow
  field show : A → String
open Show ⦃...⦄ public
