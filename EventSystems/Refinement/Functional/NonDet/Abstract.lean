
/-
  Reuse of abstract events (functional refinement)
-/

import EventSystems.Refinement.Functional.NonDet.Basic
import EventSystems.Refinement.Relational.NonDet.Abstract

open Refinement
open FRefinement

structure _AbstractFRNDEventSpec (AM) [Machine ACTX AM]
                                 (M) [Machine CTX M]
                                 [FRefinement AM M] (α) where

  unlift (am am' : AM) (m : M) (x : α): M

def _AbstractFRNDEventSpec.to_AbstractREventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : _AbstractFRNDEventSpec AM M α) : _AbstractREventSpec AM M α :=
  {
    lift := lift
    lift_ref := lift_ref
    refine_uniq := refine_uniq
    unlift := ev.unlift
  }

structure AbstractFRNDEventSpec (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                            [FRefinement AM M] (α) (β)
          extends _AbstractFRNDEventSpec AM M α where

  event : OrdinaryNDEvent AM α β

  step_ref (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → ∀ y, ∀ am', event.effect (lift m) x (y, am')
                  → refine am' (unlift (lift m) am' m x)

  step_safe (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → ∀ y, ∀ am', event.effect (lift m) x (y, am')
                  → Machine.invariant (unlift (lift m) am' m x)

  step_conc (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → ∀ y, ∀ m', event.effect (lift m) x (y, lift m')
                  → Machine.invariant (M:=AM) (lift m')
                  → Machine.invariant (M:=M) m'

  lift_unlift (m : M) (am am' : AM) (x : α):
    Machine.invariant m → Machine.invariant am'
    → lift (unlift am am' m x) = am'

@[simp]
def AbstractFRNDEventSpec.toAbstractRNDEventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : AbstractFRNDEventSpec AM M α β) : AbstractRNDEventSpec AM M α β :=
  {
    to_AbstractREventSpec := ev.to_AbstractREventSpec
    event := ev.event
    step_ref := ev.step_ref
    step_safe := ev.step_safe
    step_conc := ev.step_conc
    lift_unlift := ev.lift_unlift
  }

@[simp]
def newAbstractFRNDEvent [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : AbstractFRNDEventSpec AM M α β) : OrdinaryRNDEvent AM M α β :=
  newAbstractRNDEvent abs.toAbstractRNDEventSpec
