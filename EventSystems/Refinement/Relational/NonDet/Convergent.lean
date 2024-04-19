
import EventSystems.NonDet.Basic
import EventSystems.NonDet.Convergent
import EventSystems.Refinement.Relational.NonDet.Basic

open Refinement

structure _AnticipatedRNDEventPO (v) [Preorder v]  [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M] (ev : _NDEvent M α β) (kind : EventKind)
          extends _Variant v, _RNDEventPO (instR:=instR) ev kind  where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → ∀ y, ∀ m', ev.effect m x (y, m')
                → variant m' ≤ variant m

structure AnticipatedRNDEvent (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M] (α) (β) extends _NDEvent M α β where
  po : _AnticipatedRNDEventPO v (instR:=instR) to_NDEvent (EventKind.TransNonDet Convergence.Anticipated)

@[simp]
def AnticipatedRNDEvent.toAnticipatedNDEvent [Preorder v] [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : AnticipatedRNDEvent v AM M α β) : AnticipatedNDEvent v M α β :=
  { to_NDEvent := ev.to_NDEvent
    po := {
      safety := ev.po.safety
      feasibility := ev.po.feasibility
      variant := ev.po.variant
      nonIncreasing := ev.po.nonIncreasing
    }
  }

structure AnticipatedRNDEventSpecFromOrdinary (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M] (α) (β)
  extends _Variant v, RNDEventSpec AM M α β where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ y, ∀ m', effect m x (y, m')
                 → variant m' ≤ variant m

@[simp]
def AnticipatedRNDEvent_fromOrdinary [Preorder v]  [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : OrdinaryRNDEvent AM M α β)
  (variant : M → v)
  (Hnincr: ∀ (m : M) (x : α),
    Machine.invariant m
    → ev.guard m x
    → ∀ y, ∀ m', ev.effect m x (y, m') → variant m' ≤ variant m)
     : AnticipatedRNDEvent v AM M α β :=
  {
    guard := ev.guard
    effect := ev.effect
    po := {
      safety := ev.po.safety
      feasibility := ev.po.feasibility
      abstract := ev.po.abstract
      strengthening := ev.po.strengthening
      simulation := ev.po.simulation
      variant := variant
      nonIncreasing := Hnincr
    }
  }

@[simp]
def newAnticipatedRNDEventfromOrdinary [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
    (ev : AnticipatedRNDEventSpecFromOrdinary v AM M α β) : AnticipatedRNDEvent v AM M α β :=
  AnticipatedRNDEvent_fromOrdinary (newRNDEvent ev.toRNDEventSpec) ev.to_Variant.variant ev.nonIncreasing

structure AnticipatedRNDEventSpecFromOrdinary' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M] (α)
  extends _Variant v, RNDEventSpec AM M α Unit where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ m', effect m x ((), m')
            → variant m' ≤ variant m

@[simp]
def AnticipatedRNDEventSpecFromOrdinary'.toAnticipatedRNDEventSpecFromOrdinary  [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : AnticipatedRNDEventSpecFromOrdinary' v AM M α) : AnticipatedRNDEventSpecFromOrdinary v AM M α Unit :=
  {
    toRNDEventSpec := ev.toRNDEventSpec
    variant := ev.variant
    nonIncreasing := fun m x => by simp
                                   intros Hinv Hgrd _ m' Heff
                                   apply ev.nonIncreasing <;> assumption
  }

@[simp]
def newAnticipatedRNDEventfromOrdinary' [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
    (ev : AnticipatedRNDEventSpecFromOrdinary' v AM M α) : AnticipatedRNDEvent v AM M α Unit :=
  newAnticipatedRNDEventfromOrdinary ev.toAnticipatedRNDEventSpecFromOrdinary

structure AnticipatedRNDEventSpecFromOrdinary'' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  extends _Variant v, RNDEventSpec'' AM M where

  nonIncreasing (m : M):
    Machine.invariant m
    → guard m
    → ∀ m', effect m m'
            → variant m' ≤ variant m

@[simp]
def AnticipatedRNDEventSpecFromOrdinary''.toAnticipatedRNDEventSpecFromOrdinary  [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : AnticipatedRNDEventSpecFromOrdinary'' v AM M) : AnticipatedRNDEventSpecFromOrdinary v AM M Unit Unit :=
  {
    toRNDEventSpec := ev.toRNDEventSpec
    variant := ev.variant
    nonIncreasing := fun m x => by simp
                                   intros Hinv Hgrd _ m' Heff
                                   apply ev.nonIncreasing <;> assumption
  }

@[simp]
def newAnticipatedRNDEventfromOrdinary'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
    (ev : AnticipatedRNDEventSpecFromOrdinary'' v AM M) : AnticipatedRNDEvent v AM M Unit Unit :=
  newAnticipatedRNDEventfromOrdinary ev.toAnticipatedRNDEventSpecFromOrdinary

structure AnticipatedRNDEventSpecFromAnticipated (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M] (α) (β)
  extends _Variant v (M:=M), NDEventSpec M α β where

  abstract : AnticipatedNDEvent v AM α β

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ am, refine am m
      → abstract.guard am x

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ y, ∀ m', effect m x (y, m')
                   → ∀ am, refine am m
                           → ∃ am', abstract.effect am x (y, am')
                                    ∧ refine am' m'

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ y, ∀ m', effect m x (y, m')
                 → variant m' ≤ variant m

@[simp]
def newAnticipatedRNDEventfromAnticipated [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
    (ev : AnticipatedRNDEventSpecFromAnticipated v AM M α β) : AnticipatedRNDEvent v AM M α β :=
 {
  guard := ev.guard
  effect := ev.effect
  po := {
    safety := ev.safety
    feasibility := ev.feasibility
    variant := ev.variant
    abstract := ev.abstract.to_NDEvent
    strengthening := ev.strengthening
    simulation := ev.simulation
    nonIncreasing := ev.nonIncreasing
  }
 }

structure AnticipatedRNDEventSpecFromAnticipated' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M] (α)
  extends _Variant v (M:=M), NDEventSpec' M α where

  abstract : AnticipatedNDEvent v AM α Unit

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ am, refine am m
      → abstract.guard am x

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ m', effect m x m'
            → ∀ am, refine am m
                    → ∃ am', abstract.effect am x ((), am')
                             ∧ refine am' m'

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ m', effect m x m'
            → variant m' ≤ variant m

def AnticipatedRNDEventSpecFromAnticipated'.toAnticipatedRNDEventSpecFromAnticipated [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : AnticipatedRNDEventSpecFromAnticipated' v AM M α) : AnticipatedRNDEventSpecFromAnticipated v AM M α Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec
    variant := ev.variant
    nonIncreasing := fun m x => by simp
                                   intros Hinv Hgrd m' Heff
                                   apply ev.nonIncreasing <;> assumption
    abstract := ev.abstract
    strengthening := ev.strengthening
    simulation := fun m x => by simp
                                intros Hinv Hgrd _ m' Heff am Href
                                apply ev.simulation m x Hinv Hgrd m' Heff am Href
  }

@[simp]
def newAnticipatedRNDEventfromAnticipated' [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
    (ev : AnticipatedRNDEventSpecFromAnticipated' v AM M α) : AnticipatedRNDEvent v AM M α Unit :=
  newAnticipatedRNDEventfromAnticipated ev.toAnticipatedRNDEventSpecFromAnticipated

structure AnticipatedRNDEventSpecFromAnticipated'' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  extends _Variant v (M:=M), NDEventSpec'' M where

  abstract : AnticipatedNDEvent v AM Unit Unit

  strengthening (m : M):
    Machine.invariant m
    → guard m
    → ∀ am, refine am m
      → abstract.guard am ()

  simulation (m : M):
    Machine.invariant m
    → guard m
    → ∀ m', effect m m'
            → ∀ am, refine am m
                    → ∃ am', abstract.effect am () ((), am')
                             ∧ refine am' m'

  nonIncreasing (m : M):
    Machine.invariant m
    → guard m
    → ∀ m', effect m m'
            → variant m' ≤ variant m

def AnticipatedRNDEventSpecFromAnticipated''.toAnticipatedRNDEventSpecFromAnticipated [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : AnticipatedRNDEventSpecFromAnticipated'' v AM M) : AnticipatedRNDEventSpecFromAnticipated v AM M Unit Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec
    variant := ev.variant
    nonIncreasing := fun m x => by simp
                                   intros Hinv Hgrd m' Heff
                                   apply ev.nonIncreasing <;> assumption
    abstract := ev.abstract
    strengthening := fun m _ => by apply ev.strengthening
    simulation := fun m x => by simp
                                intros Hinv Hgrd _ m' Heff am Href
                                apply ev.simulation <;> assumption
  }

@[simp]
def newAnticipatedRNDEventfromAnticipated'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
    (ev : AnticipatedRNDEventSpecFromAnticipated'' v AM M) : AnticipatedRNDEvent v AM M Unit Unit :=
  newAnticipatedRNDEventfromAnticipated ev.toAnticipatedRNDEventSpecFromAnticipated

structure _ConvergentRNDEventPO (v) [Preorder v] [WellFoundedLT v]  [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M] (ev : _NDEvent M α β) (kind : EventKind)
          extends _Variant v, _AnticipatedRNDEventPO (instR:=instR) v ev kind where

  convergence (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → ∀ y, ∀ m', ev.effect m x (y, m')
                → variant m' < variant m

structure ConvergentRNDEvent (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M] (α) (β) extends _NDEvent M α β where
  po : _ConvergentRNDEventPO v (instR:=instR) to_NDEvent (EventKind.TransNonDet Convergence.Convergent)

@[simp]
def ConvergentRNDEvent.toConvergentNDEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : ConvergentRNDEvent v AM M α β) : ConvergentNDEvent v M α β :=
  { to_NDEvent := ev.to_NDEvent
    po := {
      safety := ev.po.safety
      feasibility := ev.po.feasibility
      variant := ev.po.variant
      nonIncreasing := fun m x => by simp
                                     intros Hinv Hgrd y m' Heff
                                     have Hcv := ev.po.convergence m x Hinv Hgrd y m' Heff
                                     exact le_of_lt Hcv

      convergence := ev.po.convergence
    }
  }

structure ConvergentRNDEventSpec (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M] (α) (β)
  extends _Variant v (M:=M), NDEventSpec M α β where

  abstract : _NDEvent AM α β

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ am, refine am m
      → abstract.guard am x

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ y, ∀ m', effect m x (y, m')
                   → ∀ am, refine am m
                           → ∃ am', abstract.effect am x (y, am')
                                    ∧ refine am' m'

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ y, ∀ m', effect m x (y, m')
                 → variant m' < variant m

@[simp]
def newConvergentRNDEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : ConvergentRNDEventSpec v AM M α β) : ConvergentRNDEvent v AM M α β :=
  {
    guard := ev.guard
    effect := ev.effect
    po := {
      safety := ev.safety
      feasibility := ev.feasibility
      abstract := ev.abstract
      strengthening := ev.strengthening
      simulation := ev.simulation
      variant := ev.variant
      nonIncreasing := fun m x => by simp
                                     intros Hinv Hgrd y m' Heff
                                     have Hcnv := ev.convergence m x Hinv Hgrd y m' Heff
                                     apply le_of_lt ; assumption
      convergence := ev.convergence
    }
  }

structure ConvergentRNDEventSpec' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M] (α)
  extends _Variant v (M:=M), NDEventSpec' M α where

  abstract : _NDEvent AM α Unit

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ am, refine am m
      → abstract.guard am x

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ m', effect m x m'
            → ∀ am, refine am m
                    → ∃ am', abstract.effect am x ((), am')
                             ∧ refine am' m'

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ m', effect m x m'
            → variant m' < variant m

@[simp]
def ConvergentRNDEventSpec'.toConvergentRNDEventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : ConvergentRNDEventSpec' v AM M α) : ConvergentRNDEventSpec v AM M α Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec
    abstract := ev.abstract
    strengthening := ev.strengthening
    simulation := fun m x => by simp
                                intros Hinv Hgrd _ m' Heff am Href
                                apply ev.simulation <;> assumption
    variant := ev.variant
    convergence := fun m x => by simp
                                 intros Hinv Hgrd m' Heff
                                 apply ev.convergence <;> assumption
  }

@[simp]
def newConvergentRNDEvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : ConvergentRNDEventSpec' v AM M α) : ConvergentRNDEvent v AM M α Unit :=
  newConvergentRNDEvent ev.toConvergentRNDEventSpec

structure ConvergentRNDEventSpec'' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  extends _Variant v (M:=M), NDEventSpec'' M where

  abstract : _NDEvent AM Unit Unit

  strengthening (m : M):
    Machine.invariant m
    → guard m
    → ∀ am, refine am m
      → abstract.guard am ()

  simulation (m : M):
    Machine.invariant m
    → guard m
    → ∀ m', effect m m'
            → ∀ am, refine am m
                    → ∃ am', abstract.effect am () ((), am')
                             ∧ refine am' m'

  convergence (m : M):
    Machine.invariant m
    → guard m
    → ∀ m', effect m m'
            → variant m' < variant m

@[simp]
def ConvergentRNDEventSpec''.toConvergentRNDEventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : ConvergentRNDEventSpec'' v AM M) : ConvergentRNDEventSpec v AM M Unit Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec
    abstract := ev.abstract
    strengthening := fun m _ => by apply ev.strengthening
    simulation := fun m x => by simp
                                intros Hinv Hgrd _ m' Heff am Href
                                apply ev.simulation <;> assumption
    variant := ev.variant
    convergence := fun m x => by simp
                                 intros Hinv Hgrd m' Heff
                                 apply ev.convergence <;> assumption
  }

@[simp]
def newConvergentRNDEvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : ConvergentRNDEventSpec'' v AM M) : ConvergentRNDEvent v AM M Unit Unit :=
  newConvergentRNDEvent ev.toConvergentRNDEventSpec
