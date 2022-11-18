{-# OPTIONS --safe --without-K #-}

module Interface.Show where

open import Level
open import Data.String hiding (show)

private
  variable a : Level

record Show (A : Set a) : Set a where
  field
    show : A → String

open Show ⦃...⦄ public
