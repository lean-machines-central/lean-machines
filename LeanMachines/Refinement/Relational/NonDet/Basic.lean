import LeanMachines.NonDet.Basic
import LeanMachines.NonDet.Ordinary
import LeanMachines.Refinement.Relational.Basic

open Refinement
/-!

# Relational refinement of Non-deterministic events

This module contains the principles of relational refinement
for ordinary, non-deterministic events.

-/

/-!
## Ordinary non-deterministic events
-/


/-
  This typeclass specifies the proof obligations for the refinement of events.
-/
class SafeRNDEventPO {α β α' β'} [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : NDEvent M α β) (abs : NDEvent AM α' β') [instSafeAbs : SafeNDEventPO abs kabs] [instSafeEv : SafeNDEventPO ev kev]
  {valid_kind : kev.canRefine? kabs = true} where

  lift_in : α → α'
  lift_out : β → β'

  strengthening (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → ∀ am, refine am m
      → abs.guard am (lift_in x)

  simulation (m : M) (x : α):
    (Hinv : Machine.invariant m)
    → (Hgrd : ev.guard m x)
    → ∀ y, ∀ m', ev.effect m x Hgrd (y, m')
      → ∀ am, (Href : refine am m)
        → ∃ am', abs.effect am (lift_in x) (strengthening m x Hinv Hgrd am Href) (lift_out y, am')
                 ∧ refine am' m'
