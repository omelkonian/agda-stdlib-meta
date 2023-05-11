{-# OPTIONS --safe --without-K #-}
module Class.Monad.Instances where

import Data.List as List
import Data.Maybe as Maybe
import Reflection as R
open import Function

open import Class.Monad.Core

instance
  Monad-TC : Monad R.TC
  Monad-TC = record { R }

  Monad-List : Monad List.List
  Monad-List .return = List._∷ List.[]
  Monad-List ._>>=_  = flip List.concatMap

  Monad-Maybe : Monad Maybe.Maybe
  Monad-Maybe .return = Maybe.just
  Monad-Maybe ._>>=_  = Maybe._>>=_
