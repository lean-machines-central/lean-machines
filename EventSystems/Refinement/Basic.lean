
import EventSystems.Basic
import EventSystems.Convergent

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
   (ev : _Event M α β) (kind : EventKind)
   extends _EventPO ev kind where

  abstract : _Event AM α β

  strengthening (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → ∀ am, refine am m
      → abstract.guard am x

  simulation (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → ∀ am, refine am m
      -- XXX : some constraint on output ?
      --       (maybe a post_weakening requirement ?)
      --       for now, let's go with equality because its transparent for the Event-B
      --       refinement model
      → let (y, m') := ev.action m x
        let (z, am') := abstract.action am x
        y = z ∧ refine am' m'


structure OrdinaryREvent (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M] (α) (β) extends _Event M α β where
  po : _REventPO (instR:=instR) to_Event (EventKind.TransDet Convergence.Ordinary)

structure REventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M] (α) (β)
  extends EventSpec M α β where

  abstract : OrdinaryEvent AM α β

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ am, refine am m
      → abstract.guard am x

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ am, refine am m
      → let (y, m') := action m x
        let (z, am') := abstract.action am x
        y = z ∧ refine am' m'

@[simp]
def newREvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (ev : REventSpec AM M α β) : OrdinaryREvent AM M α β :=
  {
    to_Event := _Event_from_EventSpec ev.toEventSpec
    po := {
      safety := ev.safety
      abstract := ev.abstract.to_Event
      strengthening := ev.strengthening
      simulation := ev.simulation
    }
  }

structure REventSpec' (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M] (α)
  extends EventSpec' M α where

  abstract : OrdinaryEvent AM α Unit

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ am, refine am m
      → abstract.guard am x

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ am, refine am m
      → let m' := action m x
        let (z, am') := abstract.action am x
        z = () ∧ refine am' m'

@[simp]
def REventSpec_from_REventSpec' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]  (ev : REventSpec' AM M α) : REventSpec AM M α Unit :=
  {
    guard := ev.guard
    action := fun m x => ((), ev.action m x)
    safety := ev.safety
    abstract := ev.abstract
    strengthening := ev.strengthening
    simulation := ev.simulation
  }

@[simp]
def newREvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (ev : REventSpec' AM M α) : OrdinaryREvent AM M α Unit :=
  newREvent (REventSpec_from_REventSpec' ev)

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
        let (z, am') := abstract.action am ()
        z = () ∧ refine am' m'

@[simp]
def REventSpec_from_REventSpec'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]  (ev : REventSpec'' AM M) : REventSpec AM M Unit Unit :=
  {
    guard := fun m () => ev.guard m
    action := fun m () => ((), ev.action m)
    safety := fun m () => ev.safety m
    abstract := ev.abstract
    strengthening := fun m () => ev.strengthening m
    simulation := fun m () => ev.simulation m
  }

@[simp]
def newREvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (ev : REventSpec'' AM M) : OrdinaryREvent AM M Unit Unit :=
  newREvent (REventSpec_from_REventSpec'' ev)

structure InitREventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M] (α) (β)
  extends InitEventSpec M α β where

  abstract : OrdinaryEvent AM α β

  strengthening (x : α):
    guard x
    → abstract.guard Machine.reset x

  simulation (x : α):
    guard x
    → let (y, m') := init x
      let (z, am') := abstract.action Machine.reset x
      y = z ∧ refine am' m'

@[simp]
def REventSpec_from_InitREventSpec [instAM: Machine ACTX AM] [instM: Machine CTX M] [instR: Refinement AM M] (ev : InitREventSpec AM M α β) : REventSpec AM M α β :=
  {
    toEventSpec := EventSpec_from_InitEventSpec ev.toInitEventSpec
    abstract := ev.abstract
    strengthening := fun m x => by simp
                                   intros _ Hm Hgrd am Href
                                   simp [Hm] at Href
                                   have Ham := @Refinement.refine_reset ACTX AM instAM CTX M instM instR am Href
                                   have Hstr := ev.strengthening x Hgrd
                                   simp [Ham, Hstr]

    simulation := fun m x => by simp
                                intros _ Hm Hgrd am Href
                                rw [Hm] at Href
                                have Ham := @Refinement.refine_reset ACTX AM instAM CTX M instM instR am Href
                                simp [Ham]
                                have Hsim := ev.simulation x Hgrd
                                cases Hsim
                                case intro Hsim₁ Hsim₂ =>
                                  simp [Hsim₁, Hsim₂]


  }

@[simp]
def newInitREvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (ev : InitREventSpec AM M α β) : OrdinaryREvent AM M α β :=
  newREvent (REventSpec_from_InitREventSpec ev)

structure InitREventSpec' (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M] (α)
  extends InitEventSpec' M α where

  abstract : OrdinaryEvent AM α Unit

  strengthening (x : α):
    guard x
    → abstract.guard Machine.reset x

  simulation (x : α):
    guard x
    → let m' := init x
      let (z, am') := abstract.action Machine.reset x
      z = () ∧ refine am' m'

@[simp]
def InitREventSpec_from_InitREventSpec' [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (ev : InitREventSpec' AM M α) : InitREventSpec AM M α Unit :=
  {
    guard := ev.guard
    init := fun x => ((), ev.init x)
    safety := ev.safety
    abstract := ev.abstract
    strengthening := ev.strengthening
    simulation := ev.simulation
  }

@[simp]
def newInitREvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (ev : InitREventSpec' AM M α) : OrdinaryREvent AM M α Unit :=
  newREvent (REventSpec_from_InitREventSpec (InitREventSpec_from_InitREventSpec' ev))

structure InitREventSpec'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  extends InitEventSpec'' M  where

  abstract : OrdinaryEvent AM Unit Unit

  strengthening (x : α):
    guard
    → abstract.guard Machine.reset ()

  simulation (x : α):
    guard
    → let m' := init
      let (z, am') := abstract.action Machine.reset ()
      z = () ∧ refine am' m'

@[simp]
def InitREventSpec_from_InitREventSpec'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (ev : InitREventSpec'' AM M) : InitREventSpec AM M Unit Unit :=
  {
    guard := fun () => ev.guard
    init := fun () => ((), ev.init)
    safety := fun () => ev.safety
    abstract := ev.abstract
    strengthening := ev.strengthening
    simulation := ev.simulation
  }

@[simp]
def newInitREvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (ev : InitREventSpec'' AM M) : OrdinaryREvent AM M Unit Unit :=
  newREvent (REventSpec_from_InitREventSpec (InitREventSpec_from_InitREventSpec'' ev))
