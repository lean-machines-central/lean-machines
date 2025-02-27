
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
  (ev : Event M α β) (abs : Event AM α' β') [SafeEvent abs] {valid_kind : ev.kind.refine? abs.kind = true} extends (SafeEvent ev ) where

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


class RefineDefault (AM) (M) [Machine ACTX AM] [Machine CTX M] [Inhabited AM] [Inhabited M]  [Refinement AM M] where
  refine_default (am : AM) (m : M) : m = default → refine am m → am = default


instance [DecidableEq M] [DecidableEq AM] [Machine ACTX AM] [Machine CTX M] [instR : Refinement AM M]
    [Inhabited AM] [Inhabited M] [instRDef : RefineDefault AM M]
   (ev : InitEvent M α β ) (abs : InitEvent AM α' β') [SafeInitEvent abs]
   [instSafeInitR : SafeInitREvent ev abs] :

   SafeREvent ev.toEvent abs.toEvent
    (valid_kind := by simp[EventKind.refine?]) -- The proof is not automatic
where
    lift_in := instSafeInitR.lift_in
    lift_out := instSafeInitR.lift_out

    strengthening m x :=
      by
        simp
        intros hinv hdef hgrd am href
        apply And.intro
        case left =>
          apply instRDef.refine_default am m hdef href
        case right =>
          exact SafeInitREvent.strengthening x hgrd
    simulation m x hinv hgrd am href := SafeInitREvent.simulation x (InitEvent.toEvent.proof_1 ev m x hgrd)
