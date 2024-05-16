

import EventSystems.NonDet.Basic
import EventSystems.NonDet.Ordinary

import EventSystems.Refinement.Relational.Basic
import EventSystems.Refinement.Relational.NonDet.Convergent

open Refinement

structure ConcreteRNDEventSpec (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M] (α) (β)
  extends _Variant v (M:=M), NDEventSpec M α β where

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ y, ∀ m', effect m x (y, m')
                   → ∀ am, refine am m
                           → refine (self:=instR) am m'

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ y, ∀ m', effect m x (y, m')
                 → variant m' < variant m

@[simp]
def newConcreteRNDEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : ConcreteRNDEventSpec v AM M α β) : ConvergentRNDEvent v AM M α β :=
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

structure ConcreteRNDEventSpec' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M] (α)
  extends _Variant v (M:=M), NDEventSpec' M α where

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ m', effect m x m'
            → ∀ am, refine am m
                    → refine (self:=instR) am m'

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ m', effect m x m'
            → variant m' < variant m

@[simp]
def ConcreteRNDEventSpec'.toConcreteRNDEventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : ConcreteRNDEventSpec' v AM M α) : ConcreteRNDEventSpec v AM M α Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec
    variant := ev.variant
    simulation := fun m x => by simp ; apply ev.simulation
    convergence := fun m x => by simp ; apply ev.convergence
  }

@[simp]
def newConcreteRNDEvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : ConcreteRNDEventSpec' v AM M α) : ConvergentRNDEvent v AM M α Unit :=
  newConcreteRNDEvent ev.toConcreteRNDEventSpec

structure ConcreteRNDEventSpec'' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  extends _Variant v (M:=M), NDEventSpec'' M where

  simulation (m : M):
    Machine.invariant m
    → guard m
    → ∀ m', effect m m'
            → ∀ am, refine am m
                    → refine (self:=instR) am m'

  convergence (m : M):
    Machine.invariant m
    → guard m
    → ∀ m', effect m m'
            → variant m' < variant m

@[simp]
def ConcreteRNDEventSpec''.toConcreteRNDEventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : ConcreteRNDEventSpec'' v AM M) : ConcreteRNDEventSpec v AM M Unit Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec
    variant := ev.variant
    simulation := fun m => by simp ; apply ev.simulation
    convergence := fun m => by simp ; apply ev.convergence
  }

@[simp]
def newConcreteNDEvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : ConcreteRNDEventSpec'' v AM M) : ConvergentRNDEvent v AM M Unit Unit :=
  newConcreteRNDEvent ev.toConcreteRNDEventSpec
