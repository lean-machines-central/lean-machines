
import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary

/-!

# Relational refinement

This module contains the basic definitions of the relational
refinement principles for LeanMachines.

This is heavily inspired by the Event-B refinement principles
with some slight differences:

  - concrete events are not obligatory convergent (but may be, of course)
  - event merging is only indirectly supported
  - events can be composed in various ways, and machines do not directly
    integrate events.
  - alternative (and compatible) refinement principles may be (and are) proposed

-/

/-!

## Machine refinement

-/

/-- The typeclass definition for the functional refinement
of an abstract machine type `AM` (in context `ACTX`) by
 a (more) concrete machine type `M` (in context `CTX`).
-/

class Refinement {ACTX : outParam (Type u₁)} (AM)
                 [Machine ACTX AM]
                 {CTX : outParam (Type u₂)} (M)
                 [Machine CTX M] where

  /-- The relation between the abstract machine type `AM` and
   the concrete machine type `M`, defined as a type-theoretic proposition. -/
  refine : AM → M → Prop

  /-- The safety requirement of refinement. -/
  refine_safe (am : AM) (m : M):
    Machine.invariant m
    → refine am m
    → Machine.invariant am

open Refinement

/-!

## Event refinement

### Ordinary transitional events

-/


/-
  This typeclass specifies the proof obligations for the refinement of events.
-/

class SafeREvent {α β α' β'} [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : Event M α β) (abs : Event AM α' β') extends (SafeEvent ev) where

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
    → ∀ am, (Href: refine am m)
      -- XXX : some constraint on output ?
      --       (maybe a post_weakening requirement ?)
      --       for now, let's go with equality because its transparent for the Event-B
      --       refinement model
      → let (y, m') := ev.action m x Hgrd
        let (z, am') := abs.action am (lift_in x) (strengthening m x Hinv Hgrd am Href)
        lift_out y = z ∧ refine am' m'





/-!
### Ordinary initialization events
-/


/-
  We follow the same idea as for SafeInitEvent : the typeclass specifies the refinement of initialisation
  events and then allows a conversion to regular refined events
-/

class SafeInitREvent  {α β α' β'} [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : InitEvent M α β) (abs : InitEvent AM α' β')
extends SafeInitEvent ev where
  lift_in : α → α'
  lift_out : β → β'

  strengthening (x : α) : ev.guard x → abs.guard (lift_in x)

  simulation (x : α) :
    (Hgrd : ev.guard x) →
      let (y, m') := ev.init x Hgrd
      let (z, am') := abs.init (lift_in x) (strengthening x Hgrd)
      lift_out y = z ∧ refine am' m'


instance [DecidableEq M] [DecidableEq AM] [Machine ACTX AM] [Machine CTX M] [instR : Refinement AM M]
   (ev : InitEvent M α β ) (abs : InitEvent AM α' β') [instSafeInitR : SafeInitREvent ev abs]: SafeREvent ev.to_Event abs.to_Event where
    lift_in := instSafeInitR.lift_in
    lift_out := instSafeInitR.lift_out

    strengthening m x :=
      by
        simp
        intros hinv hdef hgrd am href
        apply And.intro
        case left =>
          sorry
        case right =>
          exact SafeInitREvent.strengthening x hgrd
    simulation m x hinv hgrd am href := SafeInitREvent.simulation x (InitEvent.to_Event.proof_1 ev m x hgrd)
