
import EventSystems.Event.Basic
import EventSystems.Event.Ordinary
import EventSystems.Event.Convergent

class Refinement {ACTX : outParam (Type u₁)} (AM)
                 [Machine ACTX AM]
                 {CTX : outParam (Type u₂)} (M)
                 [Machine CTX M] where

  refine : AM → M → Prop

  refine_safe (am : AM) (m : M):
    Machine.invariant m
    → refine am m
    → Machine.invariant am

  refine_reset (am : AM):
    refine am Machine.reset
    → am = Machine.reset

open Refinement

structure _REventPO  [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
   (ev : _Event M α β) (kind : EventKind) (α' β')
   extends _EventPO ev kind where

  abstract : _Event AM α' β'

  lift_in : α → α'
  lift_out : β → β'

  strengthening (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → ∀ am, refine am m
      → abstract.guard am (lift_in x)

  simulation (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → ∀ am, refine am m
      -- XXX : some constraint on output ?
      --       (maybe a post_weakening requirement ?)
      --       for now, let's go with equality because its transparent for the Event-B
      --       refinement model
      → let (y, m') := ev.action m x
        let (z, am') := abstract.action am (lift_in x)
        lift_out y = z ∧ refine am' m'

structure OrdinaryREvent (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  (α β) (α':=α) (β':=β) extends _Event M α β where
  po : _REventPO (instR:=instR) to_Event (EventKind.TransDet Convergence.Ordinary) α' β'

@[simp]
def OrdinaryREvent.toOrdinaryEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : OrdinaryREvent AM M α β α' β') : OrdinaryEvent M α β :=
  {
    to_Event := ev.to_Event
    po := ev.po.to_EventPO
  }

structure _REventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  {α β α' β'} (abstract : _Event AM α' β')
  extends EventSpec M α β where

  lift_in : α → α'
  lift_out : β → β'

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ am, refine am m
      → abstract.guard am (lift_in x)

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ am, refine am m
      → let (y, m') := action m x
        let (z, am') := abstract.action am (lift_in x)
        lift_out y = z ∧ refine am' m'

structure REventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  {α β α' β'} (abstract : OrdinaryEvent AM α' β')
  extends _REventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abstract.to_Event where

  --abstract : OrdinaryEvent AM α' β' := abstract


@[simp]
def newREvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM α' β') (ev : REventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : OrdinaryREvent AM M α β α' β' :=
  {
    to_Event := ev.to_Event
    po := {
      safety := ev.safety
      abstract := abs.to_Event
      strengthening := ev.strengthening
      simulation := ev.simulation
    }
  }

@[simp]
def newREvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM α' Unit) (ev : REventSpec AM M (α:=α) (β:=Unit) (α':=α') (β':=Unit) abs) : OrdinaryREvent AM M α Unit α' Unit :=
  newREvent abs ev

@[simp]
def newREvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM Unit Unit) (ev : REventSpec AM M (α:=Unit) (β:=Unit) (α':=Unit) (β':=Unit) abs) : OrdinaryREvent AM M Unit Unit Unit Unit :=
  newREvent abs ev

/--/ Initialization events -/

structure _InitREventPO  [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
   (ev : _Event M α β) (kind : EventKind) (α' β')
   extends _InitEventPO ev kind where

  abstract : _Event AM α' β'

  lift_in : α → α'
  lift_out : β → β'

  strengthening (x : α):
    ev.guard Machine.reset x
    → ∀ am, refine (self:=instR) am Machine.reset
      → abstract.guard am (lift_in x)

  simulation (x : α):
     ev.guard Machine.reset x
    → ∀ am, refine (self:=instR) am Machine.reset
      -- XXX : some constraint on output ?
      --       (maybe a post_weakening requirement ?)
      --       for now, let's go with equality because its transparent for the Event-B
      --       refinement model
      → let (y, m') := ev.action Machine.reset x
        let (z, am') := abstract.action am (lift_in x)
        lift_out y = z ∧ refine am' m'

structure InitREvent (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  (α) (β) (α':=α) (β':=β)
  extends _Event M α β where
  po : _InitREventPO (instR:=instR) to_Event (EventKind.InitDet) α' β'

@[simp]
def InitREvent.toInitEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (ev : InitREvent AM M α β α' β') : InitEvent M α β :=
{
  to_Event:= ev.to_Event
  po := ev.po.to_InitEventPO
}

@[simp]
def InitREvent.init  [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (ev : InitREvent AM M α β α' β') (x : α) : β × M :=
  ev.action Machine.reset x

@[simp]
def InitREvent.init'  [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (ev : InitREvent AM M Unit β Unit β') : β × M :=
  ev.init ()

@[simp]
def InitREvent.init''  [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (ev : InitREvent AM M Unit Unit Unit Unit) : M :=
  ev.init'.2

structure InitREventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  {α β α' β'} (abstract : InitEvent AM α' β')
  extends InitEventSpec M α β where

  lift_in : α → α'
  lift_out : β → β'

  strengthening (x : α):
    guard x
    → abstract.guard Machine.reset (lift_in x)

  simulation (x : α):
    guard x
    → let (y, m') := init x
      let (z, am') := abstract.action Machine.reset (lift_in x)
      lift_out y = z ∧ refine am' m'

@[simp]
def newInitREvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : InitEvent AM α' β')
  (ev : InitREventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : InitREvent AM M α β α' β' :=
  {
    guard := fun m x => m = Machine.reset ∧ ev.guard x
    action := fun _ x => ev.init x
    po := {
      lift_in := ev.lift_in
      lift_out := ev.lift_out
      safety := fun x => by simp
                            intros Hgrd
                            apply ev.safety x Hgrd
      abstract := abs.to_Event
      strengthening := fun x => by simp
                                   intros Hgrd am Href
                                   have Hst := ev.strengthening x Hgrd
                                   have Hax := Refinement.refine_reset am Href
                                   rw [Hax]
                                   assumption
      simulation := fun x => by simp
                                intros Hgrd am Href
                                have Hax := Refinement.refine_reset am Href
                                rw [Hax]
                                have Hsim := ev.simulation x Hgrd
                                simp at Hsim
                                assumption
    }
  }

@[simp]
def newInitREvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : InitEvent AM α' Unit)
  (ev : InitREventSpec AM M (α:=α) (β:=Unit) (α':=α') (β':=Unit) abs) : InitREvent AM M α Unit α' Unit :=
  newInitREvent abs ev

@[simp]
def newInitREvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : InitEvent AM Unit Unit)
  (ev : InitREventSpec AM M (α:=Unit) (β:=Unit) (α':=Unit) (β':=Unit) abs) : InitREvent AM M Unit Unit Unit Unit :=
  newInitREvent abs ev
