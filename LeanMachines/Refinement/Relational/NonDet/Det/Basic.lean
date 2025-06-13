
import LeanMachines.Refinement.Relational.Basic
import LeanMachines.NonDet.Ordinary

open Refinement

/-!

# Deterministic refined event from non-deterministic abstract events

This module defines the construction of deterministic events that
refine non-determistic abstract events.

-/

class SafeRDetEventPO {α β α' β'} [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : Event M α β) (abs : NDEvent AM α' β') [instSafeAbs : SafeNDEventPO abs kabs] [instSafeEv : SafeEventPO ev kev]
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
    → ∀ am, (Href : refine am m)
      → let (y, m') := ev.action m x Hgrd
        ∃ am', abs.effect am (lift_in x) (strengthening m x Hinv Hgrd am Href) (lift_out y, am')
               ∧ refine am' m'

#check  SafeRDetEventPO
