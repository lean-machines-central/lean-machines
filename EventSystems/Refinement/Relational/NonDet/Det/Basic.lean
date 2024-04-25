
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


/-  Initialization events -/

structure _InitRDetEventPO  [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
   (ev : _Event M α β) (kind : EventKind)
   extends _InitEventPO ev kind where

  abstract : InitNDEvent AM α β

  strengthening (x : α):
    ev.guard Machine.reset x
    → ∀ am, refine (self:=instR) am Machine.reset
      → abstract.guard am x

  simulation (x : α):
    ev.guard Machine.reset x
    → ∀ am, refine (self:=instR) am Machine.reset
      → let (y, m') := ev.action Machine.reset x
        ∃ am', abstract.effect am x (y, am')
               ∧ refine am' m'

structure InitRDetEvent (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M] (α) (β) extends _Event M α β where
  po : _InitRDetEventPO (instR:=instR) to_Event EventKind.InitDet

@[simp]
def InitRDetEvent.toInitEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : InitRDetEvent AM M α β) : InitEvent M α β :=
  {
    to_Event := ev.to_Event
    po := ev.po.to_InitEventPO
  }

@[simp]
def InitRDetEvent.init  [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (ev : InitRDetEvent AM M α β) (x : α) : β × M :=
  ev.action Machine.reset x

@[simp]
def InitRDetEvent.init'  [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (ev : InitRDetEvent AM M Unit β) : β × M :=
  ev.init ()

@[simp]
def InitRDetEvent.init''  [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (ev : InitRDetEvent AM M Unit Unit) : M :=
  ev.init'.2

structure InitRDetEventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M] (α) (β)
  extends InitEventSpec M α β where

  abstract : InitNDEvent AM α β

  strengthening (x : α):
    guard x
    → abstract.guard Machine.reset x

  simulation (x : α):
    guard x
    → let (y, m') := init x
      ∃ am', abstract.effect Machine.reset x (y, am')
              ∧ refine am' m'

@[simp]
def newInitRDetEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (ev : InitRDetEventSpec AM M α β) : InitRDetEvent AM M α β :=
  {
    guard := fun m x => m = Machine.reset ∧ ev.guard x
    action := fun _ x => ev.init x
    po := {
      safety := fun x => by simp
                            apply ev.safety
      abstract := ev.abstract
      strengthening := fun x => by simp
                                   intros Hgrd am Href
                                   have Hst := ev.strengthening x Hgrd
                                   have Hax := Refinement.refine_reset am Href
                                   rw [Hax]
                                   exact Hst
      simulation := fun x => by simp
                                intros Hgrd am Href
                                have Hsim := ev.simulation x Hgrd
                                simp at Hsim
                                obtain ⟨am', Hsim₁, Hsim₂⟩ := Hsim
                                exists am'
                                simp [Hsim₂]
                                have Hax := Refinement.refine_reset am Href
                                rw [Hax]
                                exact Hsim₁
    }
  }

structure InitRDetEventSpec' (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M] (α)
  extends InitEventSpec' M α where

  abstract : InitNDEvent AM α Unit

  strengthening (x : α):
    guard x
    → abstract.guard Machine.reset x

  simulation (x : α):
    guard x
    → let m' := init x
      ∃ am', abstract.effect Machine.reset x (y, am')
              ∧ refine am' m'

@[simp]
def InitRDetEventSpec'.toInitRDetEventSpec [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : InitRDetEventSpec' AM M α) : InitRDetEventSpec AM M α Unit :=
  {
    toInitEventSpec := ev.toInitEventSpec
    abstract := ev.abstract
    strengthening := ev.strengthening
    simulation := ev.simulation
  }

@[simp]
def newInitRDetEvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : InitRDetEventSpec' AM M α) : InitRDetEvent AM M α Unit :=
  newInitRDetEvent ev.toInitRDetEventSpec

structure InitRDetEventSpec'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  extends InitEventSpec'' M where

  abstract : InitNDEvent AM Unit Unit

  strengthening:
    guard
    → abstract.guard Machine.reset ()

  simulation:
    guard
    → let m' := init
      ∃ am', abstract.effect Machine.reset () ((), am')
              ∧ refine am' m'

@[simp]
def InitRDetEventSpec''.toInitRDetEventSpec [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : InitRDetEventSpec'' AM M) : InitRDetEventSpec AM M Unit Unit :=
  {
    toInitEventSpec := ev.toInitEventSpec
    abstract := ev.abstract
    strengthening := fun _ => ev.strengthening
    simulation := fun _ => ev.simulation
  }

@[simp]
def newInitRDetEvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : InitRDetEventSpec'' AM M) : InitRDetEvent AM M Unit Unit :=
  newInitRDetEvent ev.toInitRDetEventSpec
