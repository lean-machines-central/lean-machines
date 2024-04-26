
import EventSystems.NonDet.Basic

import EventSystems.Refinement.Functional.NonDet.Det.Basic
import EventSystems.Refinement.Functional.NonDet.Convergent

import EventSystems.Refinement.Relational.NonDet.Det.Convergent

open Refinement
open FRefinement

structure AnticipatedFRDetEventSpec_fromOrdinary (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M] (α) (β)
  extends FRDetEventSpec AM M α β where

  variant (m : M) : v

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let (_, m') := action m x
      variant m' ≤ variant m

@[simp]
def AnticipatedFRDetEventSpec_fromOrdinary.toAnticipatedRDetEventSpec_fromOrdinary
  [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AnticipatedFRDetEventSpec_fromOrdinary v AM M α β) : AnticipatedRDetEventSpec_fromOrdinary v AM M α β :=
  {
    toRDetEventSpec := ev.toRDetEventSpec
    variant := ev.variant
    nonIncreasing := ev.nonIncreasing
  }

@[simp]
def newAnticipatedFRDetEvent_fromOrdinary [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AnticipatedFRDetEventSpec_fromOrdinary v AM M α β) : AnticipatedRDetEvent v AM M α β :=
  newAnticipatedRDetEvent_fromOrdinary ev.toAnticipatedRDetEventSpec_fromOrdinary

structure AnticipatedFRDetEventSpec_fromOrdinary' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M] (α)
  extends FRDetEventSpec' AM M α where

  variant (m : M) : v

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := action m x
      variant m' ≤ variant m

@[simp]
def AnticipatedFRDetEventSpec_fromOrdinary'.toAnticipatedFRDetEventSpec_fromOrdinary
  [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AnticipatedFRDetEventSpec_fromOrdinary' v AM M α) : AnticipatedFRDetEventSpec_fromOrdinary v AM M α Unit :=
  {
    toFRDetEventSpec := ev.toFRDetEventSpec
    variant := ev.variant
    nonIncreasing := ev.nonIncreasing
  }

@[simp]
def newAnticipatedFRDetEvent_fromOrdinary' [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AnticipatedFRDetEventSpec_fromOrdinary' v AM M α) : AnticipatedRDetEvent v AM M α Unit :=
  newAnticipatedRDetEvent_fromOrdinary ev.toAnticipatedFRDetEventSpec_fromOrdinary.toAnticipatedRDetEventSpec_fromOrdinary

structure AnticipatedFRDetEventSpec_fromOrdinary'' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M]
  extends FRDetEventSpec'' AM M where

  variant (m : M) : v

  nonIncreasing (m : M):
    Machine.invariant m
    → guard m
    → let m' := action m
      variant m' ≤ variant m

@[simp]
def AnticipatedFRDetEventSpec_fromOrdinary''.toAnticipatedFRDetEventSpec_fromOrdinary
  [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AnticipatedFRDetEventSpec_fromOrdinary'' v AM M) : AnticipatedFRDetEventSpec_fromOrdinary v AM M Unit Unit :=
  {
    toFRDetEventSpec := ev.toFRDetEventSpec
    variant := ev.variant
    nonIncreasing := fun m _ => ev.nonIncreasing m
  }

@[simp]
def newAnticipatedFRDetEvent_fromOrdinary'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AnticipatedFRDetEventSpec_fromOrdinary'' v AM M) : AnticipatedRDetEvent v AM M Unit Unit :=
  newAnticipatedRDetEvent_fromOrdinary ev.toAnticipatedFRDetEventSpec_fromOrdinary.toAnticipatedRDetEventSpec_fromOrdinary

structure AnticipatedFRDetEventSpec_fromAnticipated (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M] (α) (β)
  extends EventSpec M α β where

  abstract : AnticipatedNDEvent v AM α β

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → abstract.guard (lift m) x

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let (y, m') := action m x
      abstract.effect (lift m) x (y, lift m')

  variant (m : M) : v

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let (_, m') := action m x
      variant m' ≤ variant m

@[simp]
def AnticipatedFRDetEventSpec_fromAnticipated.toAnticipatedRDetEventSpec_fromAnticipated
  [Preorder v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : AnticipatedFRDetEventSpec_fromAnticipated v AM M α β) : AnticipatedRDetEventSpec_fromAnticipated v AM M α β :=
  {
    toEventSpec := ev.toEventSpec

    abstract := ev.abstract

    strengthening := fun m x => by
      intros Hinv Hgrd am Href
      have Hst := ev.strengthening m x Hinv Hgrd
      have Hlr := lift_ref (self:=instFR) m Hinv
      have Huniq := refine_uniq am (lift m) m Hinv Href Hlr
      rw [Huniq]
      exact Hst

    simulation := fun m x => by
      simp
      intros Hinv Hgrd am Href
      have Hsim := ev.simulation m x Hinv Hgrd
      simp at Hsim
      exists (lift (ev.action m x).2)
      have Hlr := lift_ref (self:=instFR) m Hinv
      have Huniq := refine_uniq am (lift m) m Hinv Href Hlr
      rw [Huniq]
      simp [Hsim]
      have Hsafe := ev.safety m x Hinv Hgrd
      apply lift_ref (ev.action m x).2 Hsafe

    variant := ev.variant

    nonIncreasing := ev.nonIncreasing
  }

@[simp]
def newAnticipatedFRDetEvent_fromAnticipated [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AnticipatedFRDetEventSpec_fromAnticipated v AM M α β) : AnticipatedRDetEvent v AM M α β :=
  newAnticipatedRDetEvent_fromAnticipated ev.toAnticipatedRDetEventSpec_fromAnticipated

structure AnticipatedFRDetEventSpec_fromAnticipated' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M] (α)
  extends EventSpec' M α where

  abstract : AnticipatedNDEvent v AM α Unit

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → abstract.guard (lift m) x

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := action m x
      abstract.effect (lift m) x ((), lift m')

  variant (m : M) : v

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := action m x
      variant m' ≤ variant m

@[simp]
def AnticipatedFRDetEventSpec_fromAnticipated'.toAnticipatedFRDetEventSpec_fromAnticipated
  [Preorder v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : AnticipatedFRDetEventSpec_fromAnticipated' v AM M α) : AnticipatedFRDetEventSpec_fromAnticipated v AM M α Unit :=
  {
    toEventSpec := ev.toEventSpec
    abstract := ev.abstract
    strengthening := ev.strengthening
    simulation := ev.simulation
    variant := ev.variant
    nonIncreasing := ev.nonIncreasing
  }

@[simp]
def newAnticipatedFRDetEvent_fromAnticipated' [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AnticipatedFRDetEventSpec_fromAnticipated' v AM M α) : AnticipatedRDetEvent v AM M α Unit :=
  newAnticipatedRDetEvent_fromAnticipated ev.toAnticipatedFRDetEventSpec_fromAnticipated.toAnticipatedRDetEventSpec_fromAnticipated

structure AnticipatedFRDetEventSpec_fromAnticipated'' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M]
  extends EventSpec'' M where

  abstract : AnticipatedNDEvent v AM Unit Unit

  strengthening (m : M):
    Machine.invariant m
    → guard m
    → abstract.guard (lift m) ()

  simulation (m : M):
    Machine.invariant m
    → guard m
    → let m' := action m
      abstract.effect (lift m) () ((), lift m')

  variant (m : M) : v

  nonIncreasing (m : M):
    Machine.invariant m
    → guard m
    → let m' := action m
      variant m' ≤ variant m

@[simp]
def AnticipatedFRDetEventSpec_fromAnticipated''.toAnticipatedFRDetEventSpec_fromAnticipated
  [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AnticipatedFRDetEventSpec_fromAnticipated'' v AM M) : AnticipatedFRDetEventSpec_fromAnticipated v AM M Unit Unit :=
  {
    toEventSpec := ev.toEventSpec
    abstract := ev.abstract
    strengthening := fun m _ => ev.strengthening m
    simulation := fun m _ => ev.simulation m
    variant := ev.variant
    nonIncreasing := fun m _ => ev.nonIncreasing m
  }

@[simp]
def newAnticipatedFRDetEvent_fromAnticipated'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AnticipatedFRDetEventSpec_fromAnticipated'' v AM M) : AnticipatedRDetEvent v AM M Unit Unit :=
  newAnticipatedRDetEvent_fromAnticipated ev.toAnticipatedFRDetEventSpec_fromAnticipated.toAnticipatedRDetEventSpec_fromAnticipated

structure ConvergentFRDetEventSpec (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M] (α) (β)
  extends EventSpec M α β where

  abstract : _NDEvent AM α β

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → abstract.guard (lift m) x

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let (y, m') := action m x
      abstract.effect (lift m) x (y, lift m')

  variant (m : M) : v

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let (_, m') := action m x
      variant m' < variant m

@[simp]
def ConvergentFRDetEventSpec.toConvergentRDetEventSpec
  [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : ConvergentFRDetEventSpec v AM M α β) : ConvergentRDetEventSpec v AM M α β :=
  {
    toEventSpec := ev.toEventSpec

    abstract := ev.abstract

    strengthening := fun m x => by
      intros Hinv Hgrd am Href
      have Hst := ev.strengthening m x Hinv Hgrd
      have Hlr := lift_ref (self:=instFR) m Hinv
      have Huniq := refine_uniq am (lift m) m Hinv Href Hlr
      rw [Huniq]
      exact Hst

    simulation := fun m x => by
      simp
      intros Hinv Hgrd am Href
      have Hsim := ev.simulation m x Hinv Hgrd
      simp at Hsim
      exists (lift (ev.action m x).2)
      have Hlr := lift_ref (self:=instFR) m Hinv
      have Huniq := refine_uniq am (lift m) m Hinv Href Hlr
      rw [Huniq]
      simp [Hsim]
      have Hsafe := ev.safety m x Hinv Hgrd
      apply lift_ref (ev.action m x).2 Hsafe

    variant := ev.variant

    convergence := ev.convergence
  }

@[simp]
def newConvergentFRDetEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : ConvergentFRDetEventSpec v AM M α β) : ConvergentRDetEvent v AM M α β :=
  newConvergentRDetEvent ev.toConvergentRDetEventSpec

structure ConvergentFRDetEventSpec' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M] (α)
  extends EventSpec' M α where

  abstract : _NDEvent AM α Unit

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → abstract.guard (lift m) x

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := action m x
      abstract.effect (lift m) x ((), lift m')

  variant (m : M) : v

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := action m x
      variant m' < variant m

@[simp]
def ConvergentFRDetEventSpec'.toConvergentFRDetEventSpec
  [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : ConvergentFRDetEventSpec' v AM M α) : ConvergentFRDetEventSpec v AM M α Unit :=
  {
    toEventSpec := ev.toEventSpec
    abstract := ev.abstract
    strengthening := ev.strengthening
    simulation := ev.simulation
    variant := ev.variant
    convergence := ev.convergence
  }

@[simp]
def newConvergentFRDetEvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : ConvergentFRDetEventSpec' v AM M α) : ConvergentRDetEvent v AM M α Unit :=
  newConvergentRDetEvent ev.toConvergentFRDetEventSpec.toConvergentRDetEventSpec

structure ConvergentFRDetEventSpec'' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M]
  extends EventSpec'' M where

  abstract : _NDEvent AM α Unit

  strengthening (m : M):
    Machine.invariant m
    → guard m
    → abstract.guard (lift m) ()

  simulation (m : M):
    Machine.invariant m
    → guard m
    → let m' := action m
      abstract.effect (lift m) () ((), lift m')

  variant (m : M) : v

  convergence (m : M):
    Machine.invariant m
    → guard m
    → let m' := action m
      variant m' < variant m

@[simp]
def ConvergentFRDetEventSpec''.toConvergentFRDetEventSpec
  [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : ConvergentFRDetEventSpec'' v AM M) : ConvergentFRDetEventSpec v AM M Unit Unit :=
  {
    toEventSpec := ev.toEventSpec
    abstract := ev.abstract
    strengthening := fun m _ => ev.strengthening m
    simulation := fun m _ => ev.simulation m
    variant := ev.variant
    convergence := fun m _ => ev.convergence m
  }

@[simp]
def newConvergentFRDetEvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : ConvergentFRDetEventSpec'' v AM M) : ConvergentRDetEvent v AM M Unit Unit :=
  newConvergentRDetEvent ev.toConvergentFRDetEventSpec.toConvergentRDetEventSpec
