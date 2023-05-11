{-# OPTIONS --safe #-}

-- TODO
-- - fuel
-- - commutative ring solver
-- - fix deriving for `Term`
-- - profiling

module Everything where

open import Tactic.AnyOf
open import Tactic.Assumption
open import Tactic.Case
open import Tactic.Constrs
open import Tactic.EquationalReasoning
open import Tactic.ReduceDec

open import Tactic.Derive.DecEq
open import Tactic.Derive.Show
