
import EventSystems.NonDet.Basic
import EventSystems.NonDet.Ordinary

import EventSystems.Refinement.Functional.Basic
import EventSystems.Refinement.Functional.NonDet.Convergent

import EventSystems.Refinement.Relational.NonDet.Concrete

open Refinement
open FRefinement

structure ConcreteFRNDEventSpec (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: FRefinement AM M] (α) (β)
  extends _Variant v (M:=M), NDEventSpec M α β where

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ y, ∀ m', effect m x (y, m')
                   → (lift m') = (lift (AM:=AM) m)

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ y, ∀ m', effect m x (y, m')
                 → variant m' < variant m

@[simp]
def ConcreteFRNDEventSpec.toConcreteRNDEventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : ConcreteFRNDEventSpec v AM M α β) : ConcreteRNDEventSpec v AM M α β :=
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
def newConcreteFRNDEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : ConcreteFRNDEventSpec v AM M α β) : ConvergentRNDEvent v AM M α β :=
  newConcreteRNDEvent ev.toConcreteRNDEventSpec

structure ConcreteFRNDEventSpec' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M] (α)
  extends _Variant v (M:=M), NDEventSpec' M α where

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ m', effect m x m'
            → (lift m') = (lift (AM:=AM) m)

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ m', effect m x m'
            → variant m' < variant m

@[simp]
def ConcreteFRNDEventSpec'.toConcreteFRNDEventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : ConcreteFRNDEventSpec' v AM M α) : ConcreteFRNDEventSpec v AM M α Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec
    simulation := fun m x => by simp ; apply ev.simulation
    variant := ev.variant
    convergence := fun m x => by simp ; apply ev.convergence
  }

@[simp]
def newConcreteFRNDEvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : ConcreteFRNDEventSpec' v AM M α) : ConvergentRNDEvent v AM M α Unit :=
  newConcreteFRNDEvent ev.toConcreteFRNDEventSpec

structure ConcreteFRNDEventSpec'' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: FRefinement AM M]
  extends _Variant v (M:=M), NDEventSpec'' M where

  simulation (m : M):
    Machine.invariant m
    → guard m
    → ∀ m', effect m m'
            → (lift m') = (lift (AM:=AM) m)

  convergence (m : M):
    Machine.invariant m
    → guard m
    → ∀ m', effect m m'
            → variant m' < variant m

@[simp]
def ConcreteFRNDEventSpec''.toConcreteFRNDEventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : ConcreteFRNDEventSpec'' v AM M) : ConcreteFRNDEventSpec v AM M Unit Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec
    simulation := fun m x => by simp ; apply ev.simulation
    variant := ev.variant
    convergence := fun m x => by simp ; apply ev.convergence
  }

@[simp]
def newConcreteFRNDEvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : ConcreteFRNDEventSpec'' v AM M) : ConvergentRNDEvent v AM M Unit Unit :=
  newConcreteFRNDEvent ev.toConcreteFRNDEventSpec
