
import EventSystems.Refinement.Relational.Basic
import EventSystems.NonDet.Ordinary

open Refinement

structure _RDetEventPO  [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
   (ev : _Event M α β) (kind : EventKind)
   extends _EventPO ev kind where

  abstract : _NDEvent AM α β

  strengthening (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → ∀ am, refine am m
      → abstract.guard am x

  simulation (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → ∀ am, refine am m
      → let (y, m') := ev.action m x
        ∃ am', abstract.effect am x (y, am')
               ∧ refine am' m'

structure OrdinaryRDetEvent (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M] (α) (β) extends _Event M α β where
  po : _RDetEventPO (instR:=instR) to_Event (EventKind.TransDet Convergence.Ordinary)

@[simp]
def OrdinaryRDetEvent.toOrdinaryEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : OrdinaryRDetEvent AM M α β) : OrdinaryEvent M α β :=
  {
    to_Event := ev.to_Event
    po := ev.po.to_EventPO
  }

structure RDetEventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M] (α) (β)
  extends EventSpec M α β where

  abstract : OrdinaryNDEvent AM α β

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
        ∃ am', abstract.effect am x (y, am')
               ∧ refine am' m'

@[simp]
def newRDetEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (ev : RDetEventSpec AM M α β) : OrdinaryRDetEvent AM M α β :=
  {
    to_Event := ev.to_Event
    po := {
      safety := ev.safety
      abstract := ev.abstract.to_NDEvent
      strengthening := ev.strengthening
      simulation := ev.simulation
    }
  }

structure RDetEventSpec' (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M] (α)
  extends EventSpec' M α where

  abstract : OrdinaryNDEvent AM α Unit

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
        ∃ am', abstract.effect am x ((), am')
               ∧ refine am' m'

def RDetEventSpec'.toRDetEventSpec  [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : RDetEventSpec' AM M α) : RDetEventSpec AM M α Unit :=
  {
    toEventSpec := ev.toEventSpec
    abstract := ev.abstract
    strengthening := ev.strengthening
    simulation := ev.simulation
  }

@[simp]
def newRDetEvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : RDetEventSpec' AM M α) : OrdinaryRDetEvent AM M α Unit :=
  newRDetEvent ev.toRDetEventSpec

structure RDetEventSpec'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  extends EventSpec'' M where

  abstract : OrdinaryNDEvent AM Unit Unit

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
        ∃ am', abstract.effect am () ((), am')
               ∧ refine am' m'

def RDetEventSpec''.toRDetEventSpec  [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : RDetEventSpec'' AM M) : RDetEventSpec AM M Unit Unit :=
  {
    toEventSpec := ev.toEventSpec
    abstract := ev.abstract
    strengthening := fun m _ => ev.strengthening m
    simulation := fun m _ => ev.simulation m
  }

@[simp]
def newRDetEvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : RDetEventSpec'' AM M) : OrdinaryRDetEvent AM M Unit Unit :=
  newRDetEvent ev.toRDetEventSpec