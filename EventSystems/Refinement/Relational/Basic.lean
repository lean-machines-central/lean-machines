
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

structure OrdinaryREvent (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M] (α β) (α':=α) (β':=β)
  extends _Event M α β where
  po : _REventPO (instR:=instR) to_Event (EventKind.TransDet Convergence.Ordinary) α' β'

@[simp]
def OrdinaryREvent.toOrdinaryEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (ev : OrdinaryREvent AM M α β α' β') : OrdinaryEvent M α β :=
  {
    to_Event := ev.to_Event
    po := ev.po.to_EventPO
  }

structure REventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M] {α β α' β'}
  extends EventSpec M α β where

  abstract : OrdinaryEvent AM α' β'

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

@[simp]
def newREvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (ev : REventSpec (α:=α) (β:=β) (α':=α') (β':=β') AM M) : OrdinaryREvent AM M α β α' β' :=
  {
    to_Event := ev.to_Event
    po := {
      safety := ev.safety
      abstract := ev.abstract.to_Event
      strengthening := ev.strengthening
      simulation := ev.simulation
    }
  }

structure REventSpec' (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M] {α α'}
  extends EventSpec' M α where

  abstract : OrdinaryEvent AM α' Unit

  lift_in : α → α'

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ am, refine am m
      → abstract.guard am (lift_in x)

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ am, refine am m
      → let m' := action m x
        let ((), am') := abstract.action am (lift_in x)
        refine am' m'

@[simp]
def REventSpec'.toREventSpec [Machine ACTX AM] [Machine CTX M] [Refinement AM M]  (ev : REventSpec' AM M (α:=α) (α':=α')) : REventSpec AM M (α:=α) (β:=Unit) (α':=α') (β':=Unit) :=
  {
    lift_in := ev.lift_in
    lift_out := id
    guard := ev.guard
    action := fun m x => ((), ev.action m x)
    safety := ev.safety
    abstract := ev.abstract
    strengthening := ev.strengthening
    simulation := fun m x => by simp ; apply ev.simulation
  }

@[simp]
def newREvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : REventSpec' AM M (α:=α) (α':=α')) : OrdinaryREvent AM M α Unit α' Unit :=
  newREvent ev.toREventSpec

structure REventSpec'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  extends EventSpec'' M where

  abstract : OrdinaryEvent AM Unit Unit

  strengthening (m : M):
    Machine.invariant m
    → guard m
    → ∀ am, refine am m
      → abstract.guard am ()

  simulation (m : M):
    Machine.invariant m
    → guard m
    → ∀ am, refine am m
      → let m' := action m
        let ((), am') := abstract.action am ()
        refine am' m'

@[simp]
def REventSpec''.toREventSpec [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : REventSpec'' AM M) : REventSpec AM M (α:=Unit) (α':=Unit) (β:=Unit) (β':=Unit) :=
  {
    lift_in := id
    lift_out := id
    guard := fun m () => ev.guard m
    action := fun m () => ((), ev.action m)
    safety := fun m () => ev.safety m
    abstract := ev.abstract
    strengthening := fun m () => by simp ; apply ev.strengthening m
    simulation := fun m () => by simp ; apply ev.simulation m
  }

@[simp]
def newREvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : REventSpec'' AM M) : OrdinaryREvent AM M Unit Unit :=
  newREvent ev.toREventSpec

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

structure InitREvent (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M] (α) (β) (α':=α) (β':=β)
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

structure InitREventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M] {α β α' β'}
  extends InitEventSpec M α β where

  abstract : InitEvent AM α' β'

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
  (ev : InitREventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β')) : InitREvent AM M α β α' β' :=
  {
    guard := fun m x => m = Machine.reset ∧ ev.guard x
    action := fun _ x => ev.init x
    po := {
      lift_in := ev.lift_in
      lift_out := ev.lift_out
      safety := fun x => by simp
                            intros Hgrd
                            apply ev.safety x Hgrd
      abstract := ev.abstract.to_Event
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

structure InitREventSpec' (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M] {α α'}
  extends InitEventSpec' M α where

  abstract : InitEvent AM α' Unit

  lift_in : α → α'

  strengthening (x : α):
    guard x
    → abstract.guard Machine.reset (lift_in x)

  simulation (x : α):
    guard x
    → let m' := init x
      let ((), am') := abstract.action Machine.reset (lift_in x)
      refine am' m'

@[simp]
def InitREventSpec'.toInitREventSpec [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : InitREventSpec' AM M (α:=α) (α':=α')) : InitREventSpec AM M (α:=α) (β:=Unit) (α':=α') (β':=Unit) :=
  {
    toInitEventSpec := ev.toInitEventSpec
    abstract := ev.abstract
    lift_in := ev.lift_in
    lift_out := id
    strengthening := ev.strengthening
    simulation := fun x => by simp ; apply ev.simulation
  }

@[simp]
def newInitREvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : InitREventSpec' AM M (α:=α) (α':=α')) : InitREvent AM M α Unit α' Unit :=
  newInitREvent ev.toInitREventSpec

structure InitREventSpec'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  extends InitEventSpec'' M  where

  abstract : InitEvent AM Unit Unit

  strengthening:
    guard
    → abstract.guard Machine.reset ()

  simulation:
    guard
    → let m' := init
      let ((), am') := abstract.action Machine.reset ()
      refine am' m'

@[simp]
def InitREventSpec''.toInitREventSpec [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : InitREventSpec'' AM M) : InitREventSpec AM M (α:=Unit) (α':=Unit) (β:=Unit) (β':=Unit) :=
  {
    toInitEventSpec := ev.toInitEventSpec
    abstract := ev.abstract
    lift_in := id
    lift_out := id
    strengthening := fun () => by simp ; apply ev.strengthening
    simulation := fun () => by simp ; apply ev.simulation
  }

@[simp]
def newInitREvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : InitREventSpec'' AM M) : InitREvent AM M Unit Unit Unit Unit:=
  newInitREvent ev.toInitREventSpec
