
import EventSystems.Refinement.Functional.NonDet.Basic
import EventSystems.Refinement.Relational.NonDet.Convergent

open Refinement
open FRefinement

structure AnticipatedFRNDEventSpecFromOrdinary (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M] (α) (β)
  extends _Variant v, FRNDEventSpec AM M α β where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ y, ∀ m', effect m x (y, m')
                 → variant m' ≤ variant m

@[simp]
def AnticipatedFRNDEventSpecFromOrdinary.toAnticipatedRNDEventSpecFromOrdinary [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AnticipatedFRNDEventSpecFromOrdinary v AM M α β) : AnticipatedRNDEventSpecFromOrdinary v AM M α β :=
  {
    toRNDEventSpec := ev.toRNDEventSpec
    variant := ev.variant
    nonIncreasing := ev.nonIncreasing
  }

@[simp]
def newAnticipatedFRNDEventFromOrdinary [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AnticipatedFRNDEventSpecFromOrdinary v AM M α β) : AnticipatedRNDEvent v AM M α β :=
  newAnticipatedRNDEventfromOrdinary ev.toAnticipatedRNDEventSpecFromOrdinary

structure AnticipatedFRNDEventSpecFromOrdinary' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M] (α)
  extends _Variant v, FRNDEventSpec' AM M α where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ m', effect m x m'
            → variant m' ≤ variant m

@[simp]
def AnticipatedFRNDEventSpecFromOrdinary'.toAnticipatedFRNDEventSpecFromOrdinary [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AnticipatedFRNDEventSpecFromOrdinary' v AM M α) : AnticipatedFRNDEventSpecFromOrdinary v AM M α Unit :=
  {
    toFRNDEventSpec := ev.toFRNDEventSpec
    variant := ev.variant
    nonIncreasing := fun m x => by simp ; apply ev.nonIncreasing
  }

@[simp]
def newAnticipatedFRNDEventFromOrdinary' [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AnticipatedFRNDEventSpecFromOrdinary' v AM M α) : AnticipatedRNDEvent v AM M α Unit :=
  newAnticipatedFRNDEventFromOrdinary ev.toAnticipatedFRNDEventSpecFromOrdinary

structure AnticipatedFRNDEventSpecFromOrdinary'' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M]
  extends _Variant v, FRNDEventSpec'' AM M where

  nonIncreasing (m : M):
    Machine.invariant m
    → guard m
    → ∀ m', effect m m'
            → variant m' ≤ variant m

@[simp]
def AnticipatedFRNDEventSpecFromOrdinary''.toAnticipatedFRNDEventSpecFromOrdinary [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AnticipatedFRNDEventSpecFromOrdinary'' v AM M) : AnticipatedFRNDEventSpecFromOrdinary v AM M Unit Unit :=
  {
    toFRNDEventSpec := ev.toFRNDEventSpec
    variant := ev.variant
    nonIncreasing := fun m x => by simp ; apply ev.nonIncreasing
  }

@[simp]
def newAnticipatedFRNDEventFromOrdinary'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AnticipatedFRNDEventSpecFromOrdinary'' v AM M) : AnticipatedRNDEvent v AM M Unit Unit :=
  newAnticipatedFRNDEventFromOrdinary ev.toAnticipatedFRNDEventSpecFromOrdinary

structure AnticipatedFRNDEventSpecFromAnticipated (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instFR: FRefinement AM M] (α) (β)
  extends _Variant v (M:=M), NDEventSpec M α β where

  abstract : AnticipatedNDEvent v AM α β

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → abstract.guard (lift m) x

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ y, ∀ m', effect m x (y, m')
                  → abstract.effect (lift m) x (y, (lift m'))

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ y, ∀ m', effect m x (y, m')
                 → variant m' ≤ variant m

@[simp]
def AnticipatedFRNDEventSpecFromAnticipated.toAnticipatedRNDEventSpecFromAnticipated [Preorder v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : AnticipatedFRNDEventSpecFromAnticipated v AM M α β) : AnticipatedRNDEventSpecFromAnticipated v AM M α β :=
  {
    toNDEventSpec := ev.toNDEventSpec

    abstract := ev.abstract

    strengthening := fun m x => by
      intros Hinv Hgrd am Href
      have Hst := ev.strengthening m x Hinv Hgrd
      have Href' := lift_ref (self:=instFR) m Hinv
      have Huniq := refine_uniq (self:=instFR) am (lift m) m Hinv Href Href'
      rw [Huniq]
      exact Hst

    simulation := fun m x => by
      intros Hinv Hgrd y m' Heff am Href
      exists (lift m')
      have Hsim := ev.simulation m x Hinv Hgrd y m' Heff
      have Hinv' := ev.safety m x Hinv Hgrd y m' Heff
      have Href' := lift_ref (self:=instFR) m' Hinv'
      simp [Href']
      have Href'' := lift_ref (self:=instFR) m Hinv
      have Huniq := refine_uniq (self:=instFR) am (lift m) m Hinv Href Href''
      rw [Huniq]
      assumption

    variant := ev.variant

    nonIncreasing := ev.nonIncreasing
  }

@[simp]
def newAnticipatedFRNDEventFromAnticipated [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AnticipatedFRNDEventSpecFromAnticipated v AM M α β) : AnticipatedRNDEvent v AM M α β :=
  newAnticipatedRNDEventfromAnticipated ev.toAnticipatedRNDEventSpecFromAnticipated

structure AnticipatedFRNDEventSpecFromAnticipated' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instFR: FRefinement AM M] (α)
  extends _Variant v (M:=M), NDEventSpec' M α where

  abstract : AnticipatedNDEvent v AM α Unit

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → abstract.guard (lift m) x

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ m', effect m x m'
            → abstract.effect (lift m) x ((), (lift m'))

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ m', effect m x m'
            → variant m' ≤ variant m

@[simp]
def AnticipatedFRNDEventSpecFromAnticipated'.toAnticipatedFRNDEventSpecFromAnticipated [Preorder v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : AnticipatedFRNDEventSpecFromAnticipated' v AM M α) : AnticipatedFRNDEventSpecFromAnticipated v AM M α Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec

    abstract := ev.abstract
    strengthening := ev.strengthening
    simulation := fun m x => by
      simp
      intros Hinv Hgrd _ m' Heff
      apply ev.simulation m x <;> assumption

    variant := ev.variant
    nonIncreasing := fun m x => by simp ; apply ev.nonIncreasing
  }

@[simp]
def newAnticipatedFRNDEventSpecFromAnticipated' [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AnticipatedFRNDEventSpecFromAnticipated' v AM M α) : AnticipatedRNDEvent v AM M α Unit :=
  newAnticipatedFRNDEventFromAnticipated ev.toAnticipatedFRNDEventSpecFromAnticipated

structure AnticipatedFRNDEventSpecFromAnticipated'' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instFR: FRefinement AM M]
  extends _Variant v (M:=M), NDEventSpec'' M where

  abstract : AnticipatedNDEvent v AM Unit Unit

  strengthening (m : M):
    Machine.invariant m
    → guard m
    → abstract.guard (lift m) ()

  simulation (m : M):
    Machine.invariant m
    → guard m
    → ∀ m', effect m m'
            → abstract.effect (lift m) () ((), (lift m'))

  nonIncreasing (m : M):
    Machine.invariant m
    → guard m
    → ∀ m', effect m m'
            → variant m' ≤ variant m

@[simp]
def AnticipatedFRNDEventSpecFromAnticipated''.toAnticipatedFRNDEventSpecFromAnticipated [Preorder v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : AnticipatedFRNDEventSpecFromAnticipated'' v AM M) : AnticipatedFRNDEventSpecFromAnticipated v AM M Unit Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec

    abstract := ev.abstract
    strengthening := fun m _ => ev.strengthening m
    simulation := fun m x => by
      simp
      intros Hinv Hgrd _ m' Heff
      apply ev.simulation m _ <;> assumption

    variant := ev.variant
    nonIncreasing := fun m x => by simp ; apply ev.nonIncreasing
  }

@[simp]
def newAnticipatedFRNDEventSpecFromAnticipated'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AnticipatedFRNDEventSpecFromAnticipated'' v AM M) : AnticipatedRNDEvent v AM M Unit Unit :=
  newAnticipatedFRNDEventFromAnticipated ev.toAnticipatedFRNDEventSpecFromAnticipated


structure ConvergentFRNDEventSpec (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M] (α) (β)
  extends _Variant v (M:=M), NDEventSpec M α β where

  abstract : _NDEvent AM α β

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → abstract.guard (lift m) x

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ y, ∀ m', effect m x (y, m')
                   → abstract.effect (lift m) x (y, lift m')

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ y, ∀ m', effect m x (y, m')
                 → variant m' < variant m

@[simp]
def ConvergentFRNDEventSpec.toConvergentRNDEventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : ConvergentFRNDEventSpec v AM M α β) : ConvergentRNDEventSpec v AM M α β :=
  {
    toNDEventSpec := ev.toNDEventSpec

    abstract := ev.abstract

    strengthening := fun m x => by
      intros Hinv Hgrd am Href
      have Hst := ev.strengthening m x Hinv Hgrd
      have Href' := lift_ref (self:=instFR) m Hinv
      have Huniq := refine_uniq (self:=instFR) am (lift m) m Hinv Href Href'
      rw [Huniq]
      exact Hst

    simulation := fun m x => by
      intros Hinv Hgrd y m' Heff am Href
      exists (lift m')
      have Hsim := ev.simulation m x Hinv Hgrd y m' Heff
      have Hinv' := ev.safety m x Hinv Hgrd y m' Heff
      have Href' := lift_ref (self:=instFR) m' Hinv'
      simp [Href']
      have Href'' := lift_ref (self:=instFR) m Hinv
      have Huniq := refine_uniq (self:=instFR) am (lift m) m Hinv Href Href''
      rw [Huniq]
      assumption

    variant := ev.variant
    convergence := ev.convergence
  }

@[simp]
def newConvergentFRNDEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : ConvergentFRNDEventSpec v AM M α β) : ConvergentRNDEvent v AM M α β :=
  newConvergentRNDEvent ev.toConvergentRNDEventSpec

structure ConvergentFRNDEventSpec' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M] (α)
  extends _Variant v (M:=M), NDEventSpec' M α where

  abstract : _NDEvent AM α Unit

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → abstract.guard (lift m) x

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ m', effect m x m'
            → abstract.effect (lift m) x ((), lift m')

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ m', effect m x m'
            → variant m' < variant m

@[simp]
def ConvergentFRNDEventSpec'.toConvergentFRNDEventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : ConvergentFRNDEventSpec' v AM M α) : ConvergentFRNDEventSpec v AM M α Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec

    abstract := ev.abstract
    strengthening := ev.strengthening
    simulation := fun m x => by
      simp
      intros Hinv Hgrd _ m' Heff
      apply ev.simulation m x <;> assumption

    variant := ev.variant
    convergence := fun m x => by simp ; apply ev.convergence
  }

@[simp]
def newConvergentFRNDEventSpec' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : ConvergentFRNDEventSpec' v AM M α) : ConvergentRNDEvent v AM M α Unit :=
  newConvergentFRNDEvent ev.toConvergentFRNDEventSpec

structure ConvergentFRNDEventSpec'' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M]
  extends _Variant v (M:=M), NDEventSpec'' M where

  abstract : _NDEvent AM Unit Unit

  strengthening (m : M):
    Machine.invariant m
    → guard m
    → abstract.guard (lift m) ()

  simulation (m : M):
    Machine.invariant m
    → guard m
    → ∀ m', effect m m'
            → abstract.effect (lift m) () ((), lift m')

  convergence (m : M):
    Machine.invariant m
    → guard m
    → ∀ m', effect m m'
            → variant m' < variant m

@[simp]
def ConvergentFRNDEventSpec''.toConvergentFRNDEventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : ConvergentFRNDEventSpec'' v AM M) : ConvergentFRNDEventSpec v AM M Unit Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec

    abstract := ev.abstract
    strengthening := fun m _ => ev.strengthening m
    simulation := fun m x => by
      simp
      intros Hinv Hgrd _ m' Heff
      apply ev.simulation m <;> assumption

    variant := ev.variant
    convergence := fun m _ => by simp ; apply ev.convergence
  }

@[simp]
def newConvergentFRNDEventSpec'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : ConvergentFRNDEventSpec'' v AM M) : ConvergentRNDEvent v AM M Unit Unit :=
  newConvergentFRNDEvent ev.toConvergentFRNDEventSpec
