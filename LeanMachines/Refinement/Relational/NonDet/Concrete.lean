

import LeanMachines.NonDet.Basic
import LeanMachines.NonDet.Ordinary

import LeanMachines.Refinement.Relational.Basic
import LeanMachines.Refinement.Relational.NonDet.Convergent

open Refinement

/- Ordinary concrete events -/

structure ConcreteRNDEventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M] (α) (β)
  extends NDEventSpec M α β where

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ y, ∀ m', effect m x (y, m')
                   → ∀ am, refine am m
                           → refine (self:=instR) am m'


@[simp]
def newConcreteRNDEvent [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : ConcreteRNDEventSpec AM M α β) : OrdinaryRNDEvent AM M α β :=
  {
    to_NDEvent := ev.toNDEventSpec.to_NDEvent
    po := {
      safety := ev.safety
      feasibility := ev.feasibility
      lift_in := id
      lift_out := id
      abstract := skip_NDEvent
      strengthening := fun m x => by simp
      simulation := fun m x => by simp ; apply ev.simulation
    }
  }

structure ConcreteRNDEventSpec' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M] (α)
  extends NDEventSpec' M α where

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ m', effect m x m'
            → ∀ am, refine am m
                    → refine (self:=instR) am m'

@[simp]
def ConcreteRNDEventSpec'.toConcreteRNDEventSpec [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : ConcreteRNDEventSpec' AM M α) : ConcreteRNDEventSpec AM M α Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec
    simulation := fun m x => by simp ; apply ev.simulation
  }

@[simp]
def newConcreteRNDEvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : ConcreteRNDEventSpec' AM M α) : OrdinaryRNDEvent AM M α Unit :=
  newConcreteRNDEvent ev.toConcreteRNDEventSpec

structure ConcreteRNDEventSpec'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  extends NDEventSpec'' M where

  simulation (m : M):
    Machine.invariant m
    → guard m
    → ∀ m', effect m m'
            → ∀ am, refine am m
                    → refine (self:=instR) am m'

@[simp]
def ConcreteRNDEventSpec''.toConcreteRNDEventSpec [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : ConcreteRNDEventSpec'' AM M) : ConcreteRNDEventSpec AM M Unit Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec
    simulation := fun m => by simp ; apply ev.simulation
  }

@[simp]
def newConcreteNDEvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : ConcreteRNDEventSpec'' AM M) : OrdinaryRNDEvent AM M Unit Unit :=
  newConcreteRNDEvent ev.toConcreteRNDEventSpec

/-  Anticipated concrete events -/

structure ConcreteAnticipatedRNDEventSpec (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M] (α) (β)
  extends _Variant v (M:=M), ConcreteRNDEventSpec AM M α β where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ y, ∀ m', effect m x (y, m')
                 → variant m' ≤ variant m

@[simp]
def newConcreteAnticipatedRNDEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : ConcreteAnticipatedRNDEventSpec v AM M α β) : AnticipatedRNDEvent v AM M α β :=
  {
    to_NDEvent := ev.toNDEventSpec.to_NDEvent
    po := {
      safety := ev.safety
      feasibility := ev.feasibility
      lift_in := id
      lift_out := id
      abstract := skip_NDEvent
      strengthening := fun m x => by simp
      simulation := fun m x => by simp ; apply ev.simulation
      variant := ev.variant
      nonIncreasing := fun m x => by
        simp
        intros Hinv Hgrd y m' Heff
        exact ev.nonIncreasing m x Hinv Hgrd y m' Heff
    }
  }

structure ConcreteAnticipatedRNDEventSpec' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M] (α)
  extends _Variant v (M:=M), ConcreteRNDEventSpec' AM M α where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ m', effect m x m'
            → variant m' ≤ variant m

@[simp]
def ConcreteAnticipatedRNDEventSpec'.toConcreteAnticipatedRNDEventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : ConcreteAnticipatedRNDEventSpec' v AM M α) : ConcreteAnticipatedRNDEventSpec v AM M α Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec
    variant := ev.variant
    simulation := fun m x => by simp ; apply ev.simulation
    nonIncreasing := fun m x => by simp ; apply ev.nonIncreasing
  }

@[simp]
def newConcreteAnticipatedRNDEvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : ConcreteAnticipatedRNDEventSpec' v AM M α) : AnticipatedRNDEvent v AM M α Unit :=
  newConcreteAnticipatedRNDEvent ev.toConcreteAnticipatedRNDEventSpec

structure ConcreteAnticipatedRNDEventSpec'' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  extends _Variant v (M:=M), ConcreteRNDEventSpec'' AM M where

  nonIncreasing (m : M):
    Machine.invariant m
    → guard m
    → ∀ m', effect m m'
            → variant m' ≤ variant m

@[simp]
def ConcreteAnticipatedRNDEventSpec''.toConcreteAnticipatedRNDEventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : ConcreteAnticipatedRNDEventSpec'' v AM M) : ConcreteAnticipatedRNDEventSpec v AM M Unit Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec
    variant := ev.variant
    simulation := fun m => by simp ; apply ev.simulation
    nonIncreasing := fun m => by simp ; apply ev.nonIncreasing
  }

@[simp]
def newConcreteAnticipatedNDEvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : ConcreteAnticipatedRNDEventSpec'' v AM M) : AnticipatedRNDEvent v AM M Unit Unit :=
  newConcreteAnticipatedRNDEvent ev.toConcreteAnticipatedRNDEventSpec


/-  Convergent concrete events -/

structure ConcreteConvergentRNDEventSpec (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M] (α) (β)
  extends _Variant v (M:=M), ConcreteRNDEventSpec AM M α β where

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ y, ∀ m', effect m x (y, m')
                 → variant m' < variant m

@[simp]
def newConcreteConvergentRNDEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : ConcreteConvergentRNDEventSpec v AM M α β) : ConvergentRNDEvent v AM M α β :=
  {
    to_NDEvent := ev.toNDEventSpec.to_NDEvent
    po := {
      safety := ev.safety
      feasibility := ev.feasibility
      lift_in := id
      lift_out := id
      abstract := skip_NDEvent
      strengthening := fun m x => by simp
      simulation := fun m x => by simp ; apply ev.simulation
      variant := ev.variant
      nonIncreasing := fun m x => by simp
                                     intros Hinv Hgrd y m' Heff
                                     have Hcv := ev.convergence m x Hinv Hgrd y m' Heff
                                     exact le_of_lt Hcv
      convergence := ev.convergence
    }
  }

structure ConcreteConvergentRNDEventSpec' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M] (α)
  extends _Variant v (M:=M), ConcreteRNDEventSpec' AM M α where

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ m', effect m x m'
            → variant m' < variant m

@[simp]
def ConcreteConvergentRNDEventSpec'.toConcreteConvergentRNDEventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : ConcreteConvergentRNDEventSpec' v AM M α) : ConcreteConvergentRNDEventSpec v AM M α Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec
    variant := ev.variant
    simulation := fun m x => by simp ; apply ev.simulation
    convergence := fun m x => by simp ; apply ev.convergence
  }

@[simp]
def newConcreteConvergentRNDEvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : ConcreteConvergentRNDEventSpec' v AM M α) : ConvergentRNDEvent v AM M α Unit :=
  newConcreteConvergentRNDEvent ev.toConcreteConvergentRNDEventSpec

structure ConcreteConvergentRNDEventSpec'' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  extends _Variant v (M:=M), ConcreteRNDEventSpec'' AM M where

  convergence (m : M):
    Machine.invariant m
    → guard m
    → ∀ m', effect m m'
            → variant m' < variant m

@[simp]
def ConcreteConvergentRNDEventSpec''.toConcreteConvergentRNDEventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : ConcreteConvergentRNDEventSpec'' v AM M) : ConcreteConvergentRNDEventSpec v AM M Unit Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec
    variant := ev.variant
    simulation := fun m => by simp ; apply ev.simulation
    convergence := fun m => by simp ; apply ev.convergence
  }

@[simp]
def newConcreteConvergentNDEvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : ConcreteConvergentRNDEventSpec'' v AM M) : ConvergentRNDEvent v AM M Unit Unit :=
  newConcreteConvergentRNDEvent ev.toConcreteConvergentRNDEventSpec
