
import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary
import LeanMachines.Event.Convergent
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


@[simp]
def EventKind.isConvergent? (k : EventKind) :=
  match k with
  | TransDet Convergence.Convergent => true
  | TransNonDet Convergence.Convergent => true
  | _ => false

@[simp]
def EventKind.isAnticipated? (k : EventKind) :=
  match k with
  | TransDet Convergence.Anticipated => true
  | TransNonDet Convergence.Anticipated => true
  | _ => false

@[simp]
def EventKind.isOrdinary? (k : EventKind) :=
  match k with
  | TransDet Convergence.Ordinary => true
  | TransNonDet Convergence.Ordinary => true
  | _ => false

/-k₁ is the concrete kind and k₂ the abstract one-/
@[simp]
def EventKind.canRefine? (k₁ k₂ : EventKind) : Bool :=
  if k₂.isConvergent? then k₁.isConvergent?
  else if k₂.isAnticipated? then (not k₁.isOrdinary?)
       else k₂.isOrdinary?
/-
  This typeclass specifies the proof obligations for the refinement of events.
-/


class SafeREventPO {α β α' β'} [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : Event M α β) (abs : Event AM α' β') [instSafeAbs : SafeEventPO abs kabs] [instSafeEv : SafeEventPO ev kev]
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

class SafeInitREventPO  {α β α' β'} [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : _InitEvent M α β) (abs : _InitEvent AM α' β') [instSafeEv : SafeInitEventPO ev] [instSafeAbs : SafeInitEventPO abs]
where
  lift_in : α → α'
  lift_out : β → β'

  strengthening (x : α) : ev.guard x → abs.guard (lift_in x)

  simulation (x : α) :
    (Hgrd : ev.guard x) →
      let (y, m') := ev.init x Hgrd
      let (z, am') := abs.init (lift_in x) (strengthening x Hgrd)
      lift_out y = z ∧ refine am' m'

structure SafeInitREvent (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR : Refinement AM M]
  {α β α' β'} (abs : InitEvent AM α' β') extends InitEvent  M α β where
  lift_in : α → α'
  lift_out : β → β'

  strengthening (x : α) : guard x → abs.guard (lift_in x)

  simulation (x : α) :
    (Hgrd : guard x) →
      let (y, m') := init x Hgrd
      let (z, am') := abs.init (lift_in x) (strengthening x Hgrd)
      lift_out y = z ∧ refine am' m'


instance [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (abs : InitEvent AM α' β') (ev : SafeInitREvent AM M abs):
  SafeInitREventPO
    (AM := AM) (M := M)
    (α := α) (β := β)
    (ev.to_InitEvent (M := M)) (abs.to_InitEvent (M := AM))
    (instSafeAbs := safeInitEventPO_InitEvent abs)
    (instSafeEv := safeInitEventPO_InitEvent ev.toInitEvent)
  where
    lift_in := ev.lift_in
    lift_out := ev.lift_out
    strengthening := ev.strengthening
    simulation := ev.simulation


def newInitREvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : InitEvent AM α' β') (ev : SafeInitREvent AM M abs (α := α) (β := β)) : SafeInitREvent AM M abs (α := α) (β := β) := ev

structure SafeInitREvent' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  { α α' } (abs : InitEvent' AM α')
  extends InitEvent' M α where
  /-- Transformation of output value: how a concrete output must be interpreted
  at the abstract level. -/
  lift_in: α → α'

  /-- Proof obligation: guard strengthening. -/
  strengthening (x : α ) : guard x → abs.guard (lift_in x)

  /-- Proof obligation: action simulation. -/
  simulation (x : α) :
    (Hgrd : guard x) →
      let m':= init x Hgrd
      let am':= abs.init (lift_in x) (strengthening x Hgrd)
      refine am' m'

instance {α} [Machine CTX M] [Machine ACTX AM] [Refinement AM M] (abs : InitEvent' AM α') :
  Coe (SafeInitREvent' (α := α) AM M abs) (SafeInitREvent AM M (α := α) (β := Unit) (Init'.coe abs) ) where
  coe ev := {
              lift_in := ev.lift_in
              lift_out := fun _ => ()
              strengthening := ev.strengthening
              simulation x hgrd :=
                by
                  simp
                  exact ev.simulation x hgrd
              guard := ev.guard
              init x grd := ((), ev.init x grd)
              safety := ev.safety
            }


@[simp]
def newInitREvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (abs : InitEvent' AM α')
  (ev : SafeInitREvent' AM M abs (α := α)) : SafeInitREvent' AM M abs (α := α) := ev


structure SafeInitREvent'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  (abs : InitEvent'' AM)
  extends InitEvent'' M where
  /-- Transformation of output value: how a concrete output must be interpreted
  at the abstract level. -/
  lift_in: α → α'

  /-- Proof obligation: guard strengthening. -/
  strengthening : guard → abs.guard

  /-- Proof obligation: action simulation. -/
  simulation:
    (Hgrd : guard ) →
      let m':= init Hgrd
      let am':= abs.init (strengthening Hgrd)
      refine am' m'

instance {α} [Machine CTX M] [Machine ACTX AM] [Refinement AM M] (abs : InitEvent'' AM ) :
  Coe (SafeInitREvent'' AM M abs) (SafeInitREvent AM M (α := α) (β := Unit) (Init''.coe abs) ) where
  coe ev := {
              lift_in := ev.lift_in
              lift_out := fun _ => ()
              strengthening _ := ev.strengthening
              simulation :=
              fun x hgrd =>
                by
                  simp
                  exact ev.simulation hgrd
              guard _ := ev.guard
              init _ grd := ((), ev.init grd)
              safety _ := ev.safety
            }


@[simp]
def newInitREvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (abs : InitEvent'' AM)
  (ev : SafeInitREvent'' AM M abs ) : SafeInitREvent'' AM M abs  := ev



-- class RefineDefault (AM) (M) [Machine ACTX AM] [Machine CTX M] [Inhabited AM] [Inhabited M]  [Refinement AM M] where
--   refine_default (am : AM) (m : M) : m = default → refine am m → am = default


-- instance [DecidableEq M] [DecidableEq AM] [Machine ACTX AM] [Machine CTX M] [instR : Refinement AM M]
--     [Inhabited AM] [Inhabited M] [instRDef : RefineDefault AM M]
--    (ev : _InitEvent M α β ) (abs : _InitEvent AM α' β') [SafeInitEventPO abs] [SafeInitEventPO ev]
--    [instSafeInitR : SafeInitREvent ev abs] :

--    SafeREventPO ev abs.toEvent (kev := EventKind.InitDet) (kabs := EventKind.InitDet)
--     (valid_kind :=
--       by
--         simp[EventKind.refine?]
--         simp[EventKind.get_status]
--       ) -- The proof is not automatic
-- where
--     lift_in := instSafeInitR.lift_in
--     lift_out := instSafeInitR.lift_out

--     strengthening m x :=
--       by
--         simp
--         intros hinv hdef hgrd am href
--         apply And.intro
--         case left =>
--           apply instRDef.refine_default am m hdef href
--         case right =>
--           exact SafeInitREvent.strengthening x hgrd
--     simulation m x hinv hgrd am href := SafeInitREvent.simulation x (InitEvent.toEvent.proof_1 ev m x hgrd)
