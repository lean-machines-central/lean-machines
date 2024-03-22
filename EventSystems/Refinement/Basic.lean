
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
def newInitREvent (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M] (ev : InitREventSpec AM M α β) : OrdinaryREvent AM M α β :=
  newREvent (REventSpec_from_InitREventSpec ev)
