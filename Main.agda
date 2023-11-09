module Main where

open import Class.MonadReader
open import Class.MonadError
open import Class.MonadTC

open import Tactics

open import Tactic.AnyOf
open import Tactic.Assumption
open import Tactic.Case
open import Tactic.Constrs
open import Tactic.EquationalReasoning
open import Tactic.Eta
open import Tactic.Intro
open import Tactic.ReduceDec

open import Tactic.Derive.DecEq
open import Tactic.Derive.Show
