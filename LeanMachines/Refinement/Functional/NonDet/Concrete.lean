
import LeanMachines.NonDet.Basic
import LeanMachines.NonDet.Ordinary

import LeanMachines.Refinement.Functional.Basic
import LeanMachines.Refinement.Functional.NonDet.Convergent

import LeanMachines.Refinement.Relational.NonDet.Concrete

open Refinement
open FRefinement

structure ConcreteFRNDEventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: FRefinement AM M] (α) (β)
  extends NDEventSpec M α β where

  simulation (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ y, ∀ m', effect m x grd (y, m')
                   → (lift m') = (lift (AM:=AM) m)

@[simp]
def ConcreteFRNDEventSpec.toConcreteRNDEventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : ConcreteFRNDEventSpec AM M α β) : ConcreteRNDEventSpec AM M α β :=
  {
    toNDEventSpec := ev.toNDEventSpec
    simulation := fun m x => by
      intros Hinv Hgrd y m' Heff am Href
      have Hsim := ev.simulation m x Hinv Hgrd y m' Heff
      simp [refine] at *
      simp [Href]
      exact id (Eq.symm Hsim)
  }

@[simp]
def newConcreteFRNDEvent [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : ConcreteFRNDEventSpec AM M α β) : OrdinaryRNDEvent AM M α β :=
  newConcreteRNDEvent ev.toConcreteRNDEventSpec

structure ConcreteFRNDEventSpec' (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M] (α)
  extends NDEventSpec' M α where

  simulation (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ m', effect m x grd m'
            → (lift m') = (lift (AM:=AM) m)

@[simp]
def ConcreteFRNDEventSpec'.toConcreteFRNDEventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : ConcreteFRNDEventSpec' AM M α) : ConcreteFRNDEventSpec AM M α Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec
    simulation := fun m x => by simp ; apply ev.simulation
  }

@[simp]
def newConcreteFRNDEvent' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : ConcreteFRNDEventSpec' AM M α) : OrdinaryRNDEvent AM M α Unit :=
  newConcreteFRNDEvent ev.toConcreteFRNDEventSpec

structure ConcreteFRNDEventSpec'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: FRefinement AM M]
  extends NDEventSpec'' M where

  simulation (m : M):
    Machine.invariant m
    → (grd : guard m)
    → ∀ m', effect m grd m'
            → (lift m') = (lift (AM:=AM) m)

@[simp]
def ConcreteFRNDEventSpec''.toConcreteFRNDEventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : ConcreteFRNDEventSpec'' AM M) : ConcreteFRNDEventSpec AM M Unit Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec
    simulation := fun m x => by simp ; apply ev.simulation
  }

@[simp]
def newConcreteFRNDEvent'' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : ConcreteFRNDEventSpec'' AM M) : OrdinaryRNDEvent AM M Unit Unit :=
  newConcreteFRNDEvent ev.toConcreteFRNDEventSpec

/- Anticipated concrete events -/

structure ConcreteAnticipatedFRNDEventSpec (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [instM:Machine CTX M] [instR: FRefinement AM M] (α) (β)
  extends _Variant v (instM:=instM), ConcreteFRNDEventSpec AM M α β where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ y, ∀ m', effect m x grd (y, m')
                 → variant m' ≤ variant m

@[simp]
def ConcreteAnticipatedFRNDEventSpec.toConcreteAnticipatedRNDEventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : ConcreteAnticipatedFRNDEventSpec v AM M α β) : ConcreteAnticipatedRNDEventSpec v AM M α β :=
  {
    toNDEventSpec := ev.toNDEventSpec
    simulation := fun m x => by
      intros Hinv Hgrd y m' Heff am Href
      have Hsim := ev.simulation m x Hinv Hgrd y m' Heff
      simp [refine] at *
      simp [Href]
      exact id (Eq.symm Hsim)

    variant := ev.variant

    nonIncreasing := ev.nonIncreasing
  }

@[simp]
def newConcreteAnticipatedFRNDEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : ConcreteAnticipatedFRNDEventSpec v AM M α β) : AnticipatedRNDEvent v AM M α β :=
  newConcreteAnticipatedRNDEvent ev.toConcreteAnticipatedRNDEventSpec

structure ConcreteAnticipatedFRNDEventSpec' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M] (α)
  extends _Variant v (M:=M), ConcreteFRNDEventSpec' AM M α where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ m', effect m x grd m'
            → variant m' ≤ variant m

@[simp]
def ConcreteAnticipatedFRNDEventSpec'.toConcreteAnticipatedFRNDEventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : ConcreteAnticipatedFRNDEventSpec' v AM M α) : ConcreteAnticipatedFRNDEventSpec v AM M α Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec
    simulation := fun m x => by simp ; apply ev.simulation
    variant := ev.variant
    nonIncreasing := fun m x => by simp ; apply ev.nonIncreasing
  }

@[simp]
def newConcreteAnticipatedFRNDEvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : ConcreteAnticipatedFRNDEventSpec' v AM M α) : AnticipatedRNDEvent v AM M α Unit :=
  newConcreteAnticipatedFRNDEvent ev.toConcreteAnticipatedFRNDEventSpec

structure ConcreteAnticipatedFRNDEventSpec'' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: FRefinement AM M]
  extends _Variant v (M:=M), ConcreteFRNDEventSpec'' AM M where

  nonIncreasing (m : M):
    Machine.invariant m
    → (grd : guard m)
    → ∀ m', effect m grd m'
            → variant m' ≤ variant m

@[simp]
def ConcreteAnticipatedFRNDEventSpec''.toConcreteAnticipatedFRNDEventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : ConcreteAnticipatedFRNDEventSpec'' v AM M) : ConcreteAnticipatedFRNDEventSpec v AM M Unit Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec
    simulation := fun m x => by simp ; apply ev.simulation
    variant := ev.variant
    nonIncreasing := fun m x => by simp ; apply ev.nonIncreasing
  }

@[simp]
def newConcreteAnticipatedFRNDEvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : ConcreteAnticipatedFRNDEventSpec'' v AM M) : AnticipatedRNDEvent v AM M Unit Unit :=
  newConcreteAnticipatedFRNDEvent ev.toConcreteAnticipatedFRNDEventSpec

/- Convergent concrete events -/

structure ConcreteConvergentFRNDEventSpec (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [instM:Machine CTX M] [instR: FRefinement AM M] (α) (β)
  extends _Variant v (instM:=instM), ConcreteFRNDEventSpec AM M α β where

  convergence (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ y, ∀ m', effect m x grd (y, m')
                 → variant m' < variant m

@[simp]
def ConcreteConvergentFRNDEventSpec.toConcreteConvergentRNDEventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : ConcreteConvergentFRNDEventSpec v AM M α β) : ConcreteConvergentRNDEventSpec v AM M α β :=
  {
    toNDEventSpec := ev.toNDEventSpec
    simulation := fun m x => by
      intros Hinv Hgrd y m' Heff am Href
      have Hsim := ev.simulation m x Hinv Hgrd y m' Heff
      simp [refine] at *
      simp [Href]
      exact id (Eq.symm Hsim)

    variant := ev.variant

    convergence := ev.convergence
  }

@[simp]
def newConcreteConvergentFRNDEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : ConcreteConvergentFRNDEventSpec v AM M α β) : ConvergentRNDEvent v AM M α β :=
  newConcreteConvergentRNDEvent ev.toConcreteConvergentRNDEventSpec

structure ConcreteConvergentFRNDEventSpec' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M] (α)
  extends _Variant v (M:=M), ConcreteFRNDEventSpec' AM M α where

  convergence (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ m', effect m x grd m'
            → variant m' < variant m

@[simp]
def ConcreteConvergentFRNDEventSpec'.toConcreteConvergentFRNDEventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : ConcreteConvergentFRNDEventSpec' v AM M α) : ConcreteConvergentFRNDEventSpec v AM M α Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec
    simulation := fun m x => by simp ; apply ev.simulation
    variant := ev.variant
    convergence := fun m x => by simp ; apply ev.convergence
  }

@[simp]
def newConcreteConvergentFRNDEvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : ConcreteConvergentFRNDEventSpec' v AM M α) : ConvergentRNDEvent v AM M α Unit :=
  newConcreteConvergentFRNDEvent ev.toConcreteConvergentFRNDEventSpec

structure ConcreteConvergentFRNDEventSpec'' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: FRefinement AM M]
  extends _Variant v (M:=M), ConcreteFRNDEventSpec'' AM M where

  convergence (m : M):
    Machine.invariant m
    → (grd : guard m)
    → ∀ m', effect m grd m'
            → variant m' < variant m

@[simp]
def ConcreteConvergentFRNDEventSpec''.toConcreteConvergentFRNDEventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : ConcreteConvergentFRNDEventSpec'' v AM M) : ConcreteConvergentFRNDEventSpec v AM M Unit Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec
    simulation := fun m x => by simp ; apply ev.simulation
    variant := ev.variant
    convergence := fun m x => by simp ; apply ev.convergence
  }

@[simp]
def newConcreteConvergentFRNDEvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : ConcreteConvergentFRNDEventSpec'' v AM M) : ConvergentRNDEvent v AM M Unit Unit :=
  newConcreteConvergentFRNDEvent ev.toConcreteConvergentFRNDEventSpec
