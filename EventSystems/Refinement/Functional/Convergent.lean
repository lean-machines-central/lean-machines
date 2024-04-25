
import EventSystems.Refinement.Functional.Basic
import EventSystems.Refinement.Relational.Convergent
import EventSystems.Event.Convergent

open Refinement
open FRefinement

structure AnticipatedFREventSpecFromOrdinary (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M] (α) (β)
  extends _Variant (M:=M) v, EventSpec M α β where

  abstract : OrdinaryEvent AM α β

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → abstract.guard (lift m) x

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let (y, m') := action m x
      let (z, am') := abstract.action (lift m) x
      y = z ∧ am' = (lift m')

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let (_, m') := action m x
      variant m' ≤ variant m

@[simp]
def newAnticipatedFREventfromOrdinary [Preorder v] [Machine ACTX AM] [Machine CTX M] [instFR:FRefinement AM M]
  (ev : AnticipatedFREventSpecFromOrdinary v AM M α β) : AnticipatedREvent v AM M α β :=
  {
    to_Event := ev.to_Event
    po := {
      safety := ev.safety
      abstract := ev.abstract.to_Event
      strengthening := fun m x => by simp
                                     intros Hinv Hgrd am Href
                                     have Hst := ev.strengthening m x Hinv Hgrd
                                     have Href' := lift_ref (self:=instFR) m Hinv
                                     have Huniq := refine_uniq (self:=instFR) am (lift m) m Hinv Href Href'
                                     rw [Huniq]
                                     assumption
      simulation := fun m x => by simp
                                  intros Hinv Hgrd am Href
                                  have Href' := lift_ref (self:=instFR) m Hinv
                                  have Huniq := refine_uniq (self:=instFR) am (lift m) m Hinv Href Href'
                                  rw [Huniq]
                                  obtain ⟨Hsim₁, Hsim₂⟩ := ev.simulation m x Hinv Hgrd
                                  simp [Hsim₁]
                                  rw [Hsim₂]
                                  apply lift_ref
                                  apply ev.safety <;> assumption

      variant := ev.variant
      nonIncreasing := ev.nonIncreasing
    }
  }

structure AnticipatedFREventSpecFromOrdinary' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M] (α)
  extends _Variant (M:=M) v, EventSpec' M α where

  abstract : OrdinaryEvent AM α Unit

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → abstract.guard (lift m) x

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := action m x
      let ((), am') := abstract.action (lift m) x
      am' = (lift m')

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := action m x
      variant m' ≤ variant m

@[simp]
def AnticipatedFREventSpecFromOrdinary'.toAnticipatedFREventSpecFromOrdinary [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AnticipatedFREventSpecFromOrdinary' v AM M α) : AnticipatedFREventSpecFromOrdinary v AM M α Unit :=
  {
    toEventSpec := ev.toEventSpec
    abstract := ev.abstract
    strengthening := ev.strengthening
    simulation := fun m x => by simp ; apply ev.simulation
    variant := ev.variant
    nonIncreasing := ev.nonIncreasing
  }

@[simp]
def newAnticipatedFREventfromOrdinary' [Preorder v] [Machine ACTX AM] [Machine CTX M] [instFR:FRefinement AM M]
  (ev : AnticipatedFREventSpecFromOrdinary' v AM M α) : AnticipatedREvent v AM M α Unit :=
  newAnticipatedFREventfromOrdinary ev.toAnticipatedFREventSpecFromOrdinary

structure AnticipatedFREventSpecFromOrdinary'' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M]
  extends _Variant (M:=M) v, EventSpec'' M where

  abstract : OrdinaryEvent AM Unit Unit

  strengthening (m : M):
    Machine.invariant m
    → guard m
    → abstract.guard (lift m) ()

  simulation (m : M):
    Machine.invariant m
    → guard m
    → let m' := action m
      let ((), am') := abstract.action (lift m) ()
      am' = (lift m')

  nonIncreasing (m : M):
    Machine.invariant m
    → guard m
    → let m' := action m
      variant m' ≤ variant m

@[simp]
def AnticipatedFREventSpecFromOrdinary''.toAnticipatedFREventSpecFromOrdinary [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AnticipatedFREventSpecFromOrdinary'' v AM M) : AnticipatedFREventSpecFromOrdinary v AM M Unit Unit :=
  {
    toEventSpec := ev.toEventSpec
    abstract := ev.abstract
    strengthening := fun m _ => ev.strengthening m
    simulation := fun m _ => by simp ; apply ev.simulation
    variant := ev.variant
    nonIncreasing := fun m _ => ev.nonIncreasing m
  }

@[simp]
def newAnticipatedFREventfromOrdinary'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AnticipatedFREventSpecFromOrdinary'' v AM M) : AnticipatedREvent v AM M Unit Unit :=
  newAnticipatedFREventfromOrdinary ev.toAnticipatedFREventSpecFromOrdinary

structure AnticipatedFREventSpecFromAnticipated (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M] (α) (β)
  extends _Variant (M:=M) v, EventSpec M α β where

  abstract : AnticipatedEvent v AM α β

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → abstract.guard (lift m) x

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let (y, m') := action m x
      let (z, am') := abstract.action (lift m) x
      y = z ∧ am' = (lift m')

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let (_, m') := action m x
      variant m' ≤ variant m

@[simp]
def newAnticipatedFREventfromAnticipated [Preorder v] [Machine ACTX AM] [Machine CTX M] [instFR:FRefinement AM M]
  (ev : AnticipatedFREventSpecFromAnticipated v AM M α β) : AnticipatedREvent v AM M α β :=
  {
    to_Event := ev.to_Event
    po := {
      safety := ev.safety
      abstract := ev.abstract.to_Event
      strengthening := fun m x => by simp
                                     intros Hinv Hgrd am Href
                                     have Hst := ev.strengthening m x Hinv Hgrd
                                     have Href' := lift_ref (self:=instFR) m Hinv
                                     have Huniq := refine_uniq (self:=instFR) am (lift m) m Hinv Href Href'
                                     rw [Huniq]
                                     assumption
      simulation := fun m x => by simp
                                  intros Hinv Hgrd am Href
                                  have Href' := lift_ref (self:=instFR) m Hinv
                                  have Huniq := refine_uniq (self:=instFR) am (lift m) m Hinv Href Href'
                                  rw [Huniq]
                                  obtain ⟨Hsim₁, Hsim₂⟩ := ev.simulation m x Hinv Hgrd
                                  simp [Hsim₁]
                                  rw [Hsim₂]
                                  apply lift_ref
                                  apply ev.safety <;> assumption

      variant := ev.variant
      nonIncreasing := ev.nonIncreasing
    }
  }

structure AnticipatedFREventSpecFromAnticipated' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M] (α)
  extends _Variant (M:=M) v, EventSpec' M α where

  abstract : AnticipatedEvent v AM α Unit

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → abstract.guard (lift m) x

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := action m x
      let ((), am') := abstract.action (lift m) x
      am' = (lift m')

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := action m x
      variant m' ≤ variant m

@[simp]
def AnticipatedFREventSpecFromAnticipated'.toAnticipatedFREventSpecFromAnticipated [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AnticipatedFREventSpecFromAnticipated' v AM M α) : AnticipatedFREventSpecFromAnticipated v AM M α Unit :=
  {
    toEventSpec := ev.toEventSpec
    abstract := ev.abstract
    strengthening := ev.strengthening
    simulation := fun m x => by simp ; apply ev.simulation
    variant := ev.variant
    nonIncreasing := ev.nonIncreasing
  }

@[simp]
def newAnticipatedFREventfromAnticipated' [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AnticipatedFREventSpecFromAnticipated' v AM M α) : AnticipatedREvent v AM M α Unit :=
  newAnticipatedFREventfromAnticipated ev.toAnticipatedFREventSpecFromAnticipated

structure AnticipatedFREventSpecFromAnticipated'' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M]
  extends _Variant (M:=M) v, EventSpec'' M where

  abstract : AnticipatedEvent v AM Unit Unit

  strengthening (m : M):
    Machine.invariant m
    → guard m
    → abstract.guard (lift m) ()

  simulation (m : M):
    Machine.invariant m
    → guard m
    → let m' := action m
      let ((), am') := abstract.action (lift m) x
      am' = (lift m')

  nonIncreasing (m : M):
    Machine.invariant m
    → guard m
    → let m' := action m
      variant m' ≤ variant m

@[simp]
def AnticipatedFREventSpecFromAnticipated''.toAnticipatedFREventSpecFromAnticipated [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AnticipatedFREventSpecFromAnticipated'' v AM M) : AnticipatedFREventSpecFromAnticipated v AM M Unit Unit :=
  {
    toEventSpec := ev.toEventSpec
    abstract := ev.abstract
    strengthening := fun m _ => ev.strengthening m
    simulation := fun m _ => by simp ; apply ev.simulation
    variant := ev.variant
    nonIncreasing := fun m _ => ev.nonIncreasing m
  }

@[simp]
def newAnticipatedFREventfromAnticipated'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AnticipatedFREventSpecFromAnticipated'' v AM M) : AnticipatedREvent v AM M Unit Unit :=
  newAnticipatedFREventfromAnticipated ev.toAnticipatedFREventSpecFromAnticipated

structure ConvergentFREventSpec (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M] (α) (β)
  extends _Variant (M:=M) v, EventSpec M α β where

  abstract : _Event AM α β

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → abstract.guard (lift m) x

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let (y, m') := action m x
      let (z, am') := abstract.action (lift m) x
      y = z ∧ am' = (lift m')

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let (_, m') := action m x
      variant m' < variant m

@[simp]
def newConvergentFREvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instFR:FRefinement AM M]
  (ev : ConvergentFREventSpec v AM M α β) : ConvergentREvent v AM M α β :=
  {
    to_Event := ev.to_Event
    po := {
      safety := ev.safety
      abstract := ev.abstract
      strengthening := fun m x => by simp
                                     intros Hinv Hgrd am Href
                                     have Hst := ev.strengthening m x Hinv Hgrd
                                     have Href' := lift_ref (self:=instFR) m Hinv
                                     have Huniq := refine_uniq (self:=instFR) am (lift m) m Hinv Href Href'
                                     rw [Huniq]
                                     assumption
      simulation := fun m x => by simp
                                  intros Hinv Hgrd am Href
                                  have Href' := lift_ref (self:=instFR) m Hinv
                                  have Huniq := refine_uniq (self:=instFR) am (lift m) m Hinv Href Href'
                                  rw [Huniq]
                                  obtain ⟨Hsim₁, Hsim₂⟩ := ev.simulation m x Hinv Hgrd
                                  simp [Hsim₁]
                                  rw [Hsim₂]
                                  apply lift_ref
                                  apply ev.safety <;> assumption

      variant := ev.variant
      nonIncreasing := fun m x => by simp
                                     intros Hinv Hgrd
                                     have Hcv := ev.convergence m x Hinv Hgrd
                                     simp at Hcv
                                     exact le_of_lt Hcv
      convergence := ev.convergence
    }
  }

structure ConvergentFREventSpec' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M] (α)
  extends _Variant (M:=M) v, EventSpec' M α where

  abstract : _Event AM α Unit

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → abstract.guard (lift m) x

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := action m x
      let ((), am') := abstract.action (lift m) x
      am' = (lift m')

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := action m x
      variant m' < variant m

@[simp]
def ConvergentFREventSpec'.toConvergentFREventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : ConvergentFREventSpec' v AM M α) : ConvergentFREventSpec v AM M α Unit :=
  {
    toEventSpec := ev.toEventSpec
    abstract := ev.abstract
    strengthening := fun m x => by apply ev.strengthening
    simulation := fun m x => by simp ; apply ev.simulation
    variant := ev.variant
    convergence := ev.convergence
  }

@[simp]
def newConvergentFREvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instFR:FRefinement AM M]
  (ev : ConvergentFREventSpec' v AM M α) : ConvergentREvent v AM M α Unit :=
  newConvergentFREvent ev.toConvergentFREventSpec

structure ConvergentFREventSpec'' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M]
  extends _Variant (M:=M) v, EventSpec'' M where

  abstract : _Event AM Unit Unit

  strengthening (m : M):
    Machine.invariant m
    → guard m
    → abstract.guard (lift m) ()

  simulation (m : M):
    Machine.invariant m
    → guard m
    → let m' := action m
      let ((), am') := abstract.action (lift m) ()
      am' = (lift m')

  convergence (m : M):
    Machine.invariant m
    → guard m
    → let m' := action m
      variant m' < variant m

@[simp]
def ConvergentFREventSpec''.toConvergentFREventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : ConvergentFREventSpec'' v AM M) : ConvergentFREventSpec v AM M Unit Unit :=
  {
    toEventSpec := ev.toEventSpec
    abstract := ev.abstract
    strengthening := fun m x => by apply ev.strengthening
    simulation := fun m x => by simp ; apply ev.simulation
    variant := ev.variant
    convergence := fun m x => by simp ; apply ev.convergence
  }

@[simp]
def newConvergentFREvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instFR:FRefinement AM M]
  (ev : ConvergentFREventSpec'' v AM M) : ConvergentREvent v AM M Unit Unit :=
  newConvergentFREvent ev.toConvergentFREventSpec
