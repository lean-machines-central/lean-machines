
import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary
import LeanMachines.Event.Convergent

class Refinement {ACTX : outParam (Type u₁)} (AM)
                 [Machine ACTX AM]
                 {CTX : outParam (Type u₂)} (M)
                 [Machine CTX M] where

  refine : AM → M → Prop

  refine_safe (am : AM) (m : M):
    Machine.invariant m
    → refine am m
    → Machine.invariant am

  /-
  Note : this one was needed at some point
  refine_reset (am : AM):
    refine am Machine.reset
    → am = Machine.reset
  -/
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

structure REventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  {α β α' β'} (abstract : OrdinaryEvent AM α' β')
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

structure REventSpec' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  {α α'} (abstract : OrdinaryEvent AM α' Unit)
  extends EventSpec' M α where

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
def REventSpec'.toREventSpec [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM α' Unit) (ev : REventSpec' AM M (α:=α) (α':=α') abs) : REventSpec AM M (α:=α) (β:=Unit) (α':=α') (β':=Unit) abs :=
  {
    toEventSpec := ev.toEventSpec
    lift_in := ev.lift_in
    lift_out := id
    strengthening := ev.strengthening
    simulation := fun m x => by simp ; apply ev.simulation m x
  }

@[simp]
def newREvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM α' Unit) (ev : REventSpec' AM M (α:=α) (α':=α') abs) : OrdinaryREvent AM M α Unit α' Unit :=
  newREvent abs ev.toREventSpec

structure REventSpec'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  (abstract : OrdinaryEvent AM Unit Unit)
  extends EventSpec'' M where

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
  (abs : OrdinaryEvent AM Unit Unit) (ev : REventSpec'' AM M abs) : REventSpec AM M (α:=Unit) (β:=Unit) (α':=Unit) (β':=Unit) abs :=
  {
    toEventSpec := ev.toEventSpec
    lift_in := id
    lift_out := id
    strengthening := fun m x => by simp ; apply ev.strengthening m
    simulation := fun m x => by simp ; apply ev.simulation m
  }

@[simp]
def newREvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM Unit Unit) (ev : REventSpec'' AM M abs) : OrdinaryREvent AM M Unit Unit :=
  newREvent abs ev.toREventSpec

/--/ Initialization events -/

structure _InitREventPO  [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
   (ev : _InitEvent M α β) (kind : EventKind) (α' β')
   extends _InitEventPO ev kind where

  abstract : _InitEvent AM α' β'

  lift_in : α → α'
  lift_out : β → β'

  strengthening (x : α):
    ev.guard x
    → abstract.guard (lift_in x)

  simulation (x : α):
     ev.guard x
    → let (y, m') := ev.init x
      let (z, am') := abstract.init (lift_in x)
      lift_out y = z ∧ refine am' m'

structure InitREvent (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  (α) (β) (α':=α) (β':=β)
  extends _InitEvent M α β where
  po : _InitREventPO (instR:=instR) to_InitEvent (EventKind.InitDet) α' β'

@[simp]
def InitREvent.toInitEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (ev : InitREvent AM M α β α' β') : InitEvent M α β :=
{
  to_InitEvent:= ev.to_InitEvent
  po := ev.po.to_InitEventPO
}

structure InitREventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  {α β α' β'} (abstract : InitEvent AM α' β')
  extends InitEventSpec M α β where

  lift_in : α → α'
  lift_out : β → β'

  strengthening (x : α):
    guard x
    → abstract.guard (lift_in x)

  simulation (x : α):
    guard x
    → let (y, m') := init x
      let (z, am') := abstract.init (lift_in x)
      lift_out y = z ∧ refine am' m'

@[simp]
def newInitREvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : InitEvent AM α' β')
  (ev : InitREventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : InitREvent AM M α β α' β' :=
  {
    to_InitEvent := ev.to_InitEvent
    po := {
      lift_in := ev.lift_in
      lift_out := ev.lift_out
      safety := fun x => by simp
                            intros Hgrd
                            apply ev.safety x Hgrd
      abstract := abs.to_InitEvent
      strengthening := fun x => by
        simp
        intros Hgrd
        apply ev.strengthening x Hgrd

      simulation := fun x => by
        simp
        intros Hgrd
        have Hsim := ev.simulation x Hgrd
        simp at Hsim
        assumption
    }
  }

structure InitREventSpec' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  {α α'} (abstract : InitEvent AM α' Unit)
  extends InitEventSpec' M α where

  lift_in : α → α'

  strengthening (x : α):
    guard x
    → abstract.guard (lift_in x)

  simulation (x : α):
    guard x
    → let m' := init x
      let ((), am') := abstract.init (lift_in x)
      refine am' m'

@[simp]
def InitREventSpec'.toInitREventSpec [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : InitEvent AM α' Unit) (ev : InitREventSpec' AM M (α:=α) (α':=α') abs) : InitREventSpec AM M (α:=α) (β:=Unit) (α':=α') (β':=Unit) abs :=
  {
    toInitEventSpec := ev.toInitEventSpec
    lift_in := ev.lift_in
    lift_out := id
    strengthening := fun x => by simp ; apply ev.strengthening
    simulation := fun x => by simp ; apply ev.simulation
  }

@[simp]
def newInitREvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : InitEvent AM α' Unit)
  (ev : InitREventSpec' AM M (α:=α) (α':=α') abs) : InitREvent AM M α Unit α' Unit :=
  newInitREvent abs ev.toInitREventSpec

structure InitREventSpec'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  (abstract : InitEvent AM Unit Unit)
  extends InitEventSpec'' M where

  strengthening:
    guard
    → abstract.guard ()

  simulation:
    guard
    → let m' := init
      let ((), am') := abstract.init ()
      refine am' m'

@[simp]
def InitREventSpec''.toInitREventSpec [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : InitEvent AM Unit Unit) (ev : InitREventSpec'' AM M abs) : InitREventSpec AM M (α:=Unit) (β:=Unit) (α':=Unit) (β':=Unit) abs :=
  {
    toInitEventSpec := ev.toInitEventSpec
    lift_in := id
    lift_out := id
    strengthening := fun () => by simp ; apply ev.strengthening
    simulation := fun () => by simp ; apply ev.simulation
  }

@[simp]
def newInitREvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : InitEvent AM Unit Unit)
  (ev : InitREventSpec'' AM M abs) : InitREvent AM M Unit Unit :=
  newInitREvent abs ev.toInitREventSpec
