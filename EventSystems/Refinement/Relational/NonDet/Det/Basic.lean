
import EventSystems.Refinement.Relational.Basic
import EventSystems.NonDet.Ordinary

open Refinement

structure _RDetEventPO  [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
   (ev : _Event M α β) (kind : EventKind) (α' β')
   extends _EventPO ev kind where

  abstract : _NDEvent AM α' β'

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
      → let (y, m') := ev.action m x
        ∃ am', abstract.effect am (lift_in x) (lift_out y, am')
               ∧ refine am' m'

structure OrdinaryRDetEvent (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  (α) (β) (α':=α) (β':=β) extends _Event M α β where
  po : _RDetEventPO (instR:=instR) to_Event (EventKind.TransDet Convergence.Ordinary) α' β'

@[simp]
def OrdinaryRDetEvent.toOrdinaryEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : OrdinaryRDetEvent AM M α β) : OrdinaryEvent M α β :=
  {
    to_Event := ev.to_Event
    po := ev.po.to_EventPO
  }

structure RDetEventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  {α β α' β'} (abstract : OrdinaryNDEvent AM α' β')
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
        ∃ am', abstract.effect am (lift_in x) (lift_out y, am')
               ∧ refine am' m'

@[simp]
def newRDetEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM α' β') (ev : RDetEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : OrdinaryRDetEvent AM M α β α' β' :=
  {
    to_Event := ev.to_Event
    po := {
      safety := ev.safety
      abstract := abs.to_NDEvent
      strengthening := ev.strengthening
      simulation := ev.simulation
    }
  }

structure RDetEventSpec' (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  {α α'} (abstract : OrdinaryNDEvent AM α' Unit)
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
        ∃ am', abstract.effect am (lift_in x) ((), am')
               ∧ refine am' m'

@[simp]
def RDetEventSpec'.toRDetEventSpec [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abstract : OrdinaryNDEvent AM α' Unit)
  (ev : RDetEventSpec' AM M (α:=α) (α':=α') abstract) : RDetEventSpec AM M (α:=α) (β:=Unit) (α':=α') (β':=Unit) abstract :=
  {
    toEventSpec := ev.toEventSpec
    lift_in := ev.lift_in
    lift_out := id
    strengthening := ev.strengthening
    simulation := ev.simulation
  }

@[simp]
def newRDetEvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM α' Unit) (ev : RDetEventSpec' AM M (α:=α) (α':=α') abs) : OrdinaryRDetEvent AM M α Unit α' Unit :=
  newRDetEvent abs ev.toRDetEventSpec

structure RDetEventSpec'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  (abstract : OrdinaryNDEvent AM Unit Unit)
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
        ∃ am', abstract.effect am () ((), am')
               ∧ refine am' m'

@[simp]
def RDetEventSpec''.toRDetEventSpec [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abstract : OrdinaryNDEvent AM Unit Unit)
  (ev : RDetEventSpec'' AM M abstract) : RDetEventSpec AM M (α:=Unit) (β:=Unit) (α':=Unit) (β':=Unit) abstract :=
  {
    toEventSpec := ev.toEventSpec
    lift_in := id
    lift_out := id
    strengthening := fun m () => ev.strengthening m
    simulation := fun m () => ev.simulation m
  }


@[simp]
def newRDetEvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit) (ev : RDetEventSpec'' AM M abs) : OrdinaryRDetEvent AM M Unit Unit :=
  newRDetEvent abs ev.toRDetEventSpec

/-  Initialization events -/

structure _InitRDetEventPO  [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
   (ev : _InitEvent M α β) (kind : EventKind) (α' β')
   extends _InitEventPO ev kind where

  abstract : InitNDEvent AM α' β'

  lift_in : α → α'
  lift_out : β → β'

  strengthening (x : α):
    ev.guard x
    → abstract.guard (lift_in x)

  simulation (x : α):
    ev.guard x
    → let (y, m') := ev.init x
      ∃ am', abstract.init (lift_in x) (lift_out y, am')
             ∧ refine am' m'

structure InitRDetEvent (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  (α) (β) (α':=α) (β':=β) extends _InitEvent M α β where
  po : _InitRDetEventPO (instR:=instR) to_InitEvent EventKind.InitDet α' β'

@[simp]
def InitRDetEvent.toInitEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : InitRDetEvent AM M α β) : InitEvent M α β :=
  {
    to_InitEvent := ev.to_InitEvent
    po := ev.po.to_InitEventPO
  }

structure InitRDetEventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  {α β α' β'} (abstract : InitNDEvent AM α' β')
  extends InitEventSpec M α β where

  lift_in : α → α'
  lift_out : β → β'

  strengthening (x : α):
    guard x
    → abstract.guard (lift_in x)

  simulation (x : α):
    guard x
    → let (y, m') := init x
      ∃ am', abstract.init (lift_in x) (lift_out y, am')
              ∧ refine am' m'

@[simp]
def newInitRDetEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : InitNDEvent AM α' β') (ev : InitRDetEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : InitRDetEvent AM M α β α' β' :=
  {
    to_InitEvent := ev.to_InitEvent
    po := {
      lift_in := ev.lift_in
      lift_out := ev.lift_out
      safety := fun x => by simp ; apply ev.safety
      abstract := abs
      strengthening := fun x => by
        simp
        intros Hgrd
        apply ev.strengthening x Hgrd

      simulation := fun x => by
        simp
        intros Hgrd
        have Hsim := ev.simulation x Hgrd
        simp at Hsim
        obtain ⟨am', Hsim₁, Hsim₂⟩ := Hsim
        exists am'
    }
  }

structure InitRDetEventSpec' (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  {α α'} (abstract : InitNDEvent AM α' Unit)
  extends InitEventSpec' M α where

  lift_in : α → α'

  strengthening (x : α):
    guard x
    → abstract.guard (lift_in x)

  simulation (x : α):
    guard x
    → let m' := init x
      ∃ am', abstract.init (lift_in x) ((), am')
              ∧ refine am' m'

@[simp]
def InitRDetEventSpec'.toInitRDetEventSpec [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abstract : InitNDEvent AM α' Unit)
  (ev : InitRDetEventSpec' AM M (α:=α) (α':=α') abstract) : InitRDetEventSpec AM M (α:=α) (β:=Unit) (α':=α') (β':=Unit) abstract :=
  {
    toInitEventSpec := ev.toInitEventSpec
    lift_in := ev.lift_in
    lift_out := id
    strengthening := ev.strengthening
    simulation := ev.simulation
  }

@[simp]
def newInitRDetEvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : InitNDEvent AM α' Unit) (ev : InitRDetEventSpec' AM M (α:=α) (α':=α') abs) : InitRDetEvent AM M α Unit α' Unit :=
  newInitRDetEvent abs ev.toInitRDetEventSpec

structure InitRDetEventSpec'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  (abstract : InitNDEvent AM Unit Unit)
  extends InitEventSpec'' M where

  strengthening:
    guard
    → abstract.guard ()

  simulation:
    guard
    → let m' := init
      ∃ am', abstract.init () ((), am')
              ∧ refine am' m'

@[simp]
def InitRDetEventSpec''.toInitRDetEventSpec [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abstract : InitNDEvent AM Unit Unit)
  (ev : InitRDetEventSpec'' AM M abstract) : InitRDetEventSpec AM M (α:=Unit) (β:=Unit) (α':=Unit) (β':=Unit) abstract :=
  {
    toInitEventSpec := ev.toInitEventSpec
    lift_in := id
    lift_out := id
    strengthening := fun () => ev.strengthening
    simulation := fun () => ev.simulation
  }

@[simp]
def newInitRDetEvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : InitNDEvent AM Unit Unit) (ev : InitRDetEventSpec'' AM M abs) : InitRDetEvent AM M Unit Unit :=
  newInitRDetEvent abs ev.toInitRDetEventSpec
