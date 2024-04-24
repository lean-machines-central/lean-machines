
import EventSystems.Refinement.Relational.Basic
import EventSystems.Event.Convergent

open Refinement

structure _AnticipatedREventPO (v) [Preorder v]  [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M] (ev : _Event M α β) (kind : EventKind)
          extends _Variant v, _REventPO (instR:=instR) ev kind  where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → let (_, m') := ev.action m x
      variant m' ≤ variant m

structure AnticipatedREvent (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M] (α) (β) extends _Event M α β where
  po : _AnticipatedREventPO v (instR:=instR) to_Event (EventKind.TransDet Convergence.Anticipated)

@[simp]
def AnticipatedREvent.toAnticipatedEvent [Preorder v] [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : AnticipatedREvent v AM M α β) : AnticipatedEvent v M α β :=
  { to_Event := ev.to_Event
    po := {
      safety := ev.po.safety
      variant := ev.po.variant
      nonIncreasing := ev.po.nonIncreasing
    } }

structure AnticipatedREventSpecFromOrdinary (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M] (α) (β)
  extends _Variant v, REventSpec AM M α β where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := (action m x).2
      variant m' ≤ variant m

@[simp]
def AnticipatedREvent_fromOrdinary [Preorder v]  [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : OrdinaryREvent AM M α β)
  (variant : M → v)
  (Hnincr: ∀ (m : M) (x : α),
    Machine.invariant m
    → ev.guard m x
    → let (_, m') := ev.action m x
      variant m' ≤ variant m) : AnticipatedREvent v AM M α β :=
  {
    guard := ev.guard
    action := ev.action
    po := {
      safety := ev.po.safety
      abstract := ev.po.abstract
      strengthening := ev.po.strengthening
      simulation := ev.po.simulation
      variant := variant
      nonIncreasing := Hnincr
    }
  }

@[simp]
def newAnticipatedREventfromOrdinary [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
    (ev : AnticipatedREventSpecFromOrdinary v AM M α β) : AnticipatedREvent v AM M α β :=
  AnticipatedREvent_fromOrdinary (newREvent ev.toREventSpec) ev.to_Variant.variant ev.nonIncreasing

structure AnticipatedREventSpecFromAnticipated (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M] (α) (β)
  extends _Variant v (M:=M), EventSpec M α β where

  abstract : AnticipatedEvent v AM α β

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

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := (action m x).2
      variant m' ≤ variant m

@[simp]
def newAnticipatedREventfromAnticipated [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
    (ev : AnticipatedREventSpecFromAnticipated v AM M α β) : AnticipatedREvent v AM M α β :=
 {
  guard := ev.guard
  action := ev.action
  po := {
    safety := ev.safety
    variant := ev.variant
    abstract := ev.abstract.to_Event
    strengthening := ev.strengthening
    simulation := ev.simulation
    nonIncreasing := ev.nonIncreasing
  }
 }

structure _ConvergentREventPO (v) [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M] (ev : _Event M α β) (kind : EventKind)
          extends _AnticipatedREventPO (instR:=instR) v ev kind where

  convergence (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → let (_, m') := ev.action m x
      variant m' < variant m

structure ConvergentREvent (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M] (α) (β) extends _Event M α β where
  po : _ConvergentREventPO v (instR:=instR) to_Event (EventKind.TransDet Convergence.Convergent)

@[simp]
def ConvergentREvent.toConvergentEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : ConvergentREvent v AM M α β) : ConvergentEvent v M α β :=
  { to_Event := ev.to_Event
    po := {
      safety := ev.po.safety
      variant := ev.po.variant
      nonIncreasing := ev.po.nonIncreasing
      convergence := ev.po.convergence
    } }

structure ConvergentREventSpec (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M] (α) (β)
  extends _Variant v (M:=M), EventSpec M α β where

  abstract : _Event AM α β

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

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := (action m x).2
      variant m' < variant m

@[simp]
def newConvergentREvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : ConvergentREventSpec v AM M α β) : ConvergentREvent v AM M α β :=
  {
    guard := ev.guard
    action := ev.action
    po := {
      safety := ev.safety
      abstract := ev.abstract
      strengthening := ev.strengthening
      simulation := ev.simulation
      variant := ev.variant
      nonIncreasing := fun m x => by simp
                                     intros Hinv Hgrd
                                     have Hcnv := ev.convergence m x Hinv Hgrd
                                     simp at Hcnv
                                     apply le_of_lt ; assumption
      convergence := ev.convergence
    }
  }

structure ConvergentREventSpec' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M] (α)
  extends _Variant v (M:=M), EventSpec' M α where

  abstract : _Event AM α Unit

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

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := (action m x)
      variant m' < variant m

@[simp]
def ConvergentREventSpec'.toConvergentREventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : ConvergentREventSpec' v AM M α) : ConvergentREventSpec v AM M α Unit :=
  {
    toEventSpec := ev.toEventSpec
    abstract := ev.abstract
    strengthening := ev.strengthening
    simulation := ev.simulation
    variant := ev.variant
    convergence := ev.convergence
  }

@[simp]
def newConvergentREvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : ConvergentREventSpec' v AM M α) : ConvergentREvent v AM M α Unit :=
  newConvergentREvent ev.toConvergentREventSpec

structure ConvergentREventSpec'' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  extends _Variant v (M:=M), EventSpec'' M where

  abstract : _Event AM Unit Unit

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

  convergence (m : M):
    Machine.invariant m
    → guard m
    → let m' := (action m)
      variant m' < variant m

@[simp]
def ConvergentREventSpec''.toConvergentREventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : ConvergentREventSpec'' v AM M) : ConvergentREventSpec v AM M Unit Unit :=
  {
    toEventSpec := ev.toEventSpec
    abstract := ev.abstract
    strengthening := fun m () => by simp ; apply ev.strengthening
    simulation := fun m () => by simp
                                 intros Hinv Hgrd am Href
                                 have Hsim := ev.simulation m Hinv Hgrd am Href
                                 simp at Hsim
                                 assumption
    variant := ev.variant
    convergence := fun m () => by simp ; apply ev.convergence
  }

@[simp]
def newConvergentREvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : ConvergentREventSpec'' v AM M) : ConvergentREvent v AM M Unit Unit :=
  newConvergentREvent ev.toConvergentREventSpec
