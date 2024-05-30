
import EventSystems.NonDet.Basic
import EventSystems.NonDet.Convergent
import EventSystems.Refinement.Relational.NonDet.Basic

open Refinement

structure _AnticipatedRNDEventPO (v) [Preorder v]  [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : _NDEvent M α β) (kind : EventKind) (α') (β')
          extends _Variant v, _RNDEventPO (instR:=instR) ev kind α' β'  where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → ∀ y, ∀ m', ev.effect m x (y, m')
                → variant m' ≤ variant m

structure AnticipatedRNDEvent (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  (α β) (α':=α) (β':=β)
  extends _NDEvent M α β where
  po : _AnticipatedRNDEventPO v (instR:=instR) to_NDEvent (EventKind.TransDet Convergence.Anticipated) α' β'

@[simp]
def AnticipatedRNDEvent.toAnticipatedNDEvent [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : AnticipatedRNDEvent v AM M α β α' β') : AnticipatedNDEvent v M α β :=
  { to_NDEvent := ev.to_NDEvent
    po := {
      safety := ev.po.safety
      feasibility := ev.po.feasibility
      variant := ev.po.variant
      nonIncreasing := ev.po.nonIncreasing
    }
  }

structure AnticipatedRNDEventSpec (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  {α β α' β'} (abs : OrdinaryNDEvent AM α' β')
  extends _Variant v, RNDEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ y, ∀ m', effect m x (y, m')
                 → variant m' ≤ variant m

@[simp]
private def _newAnticipatedRNDEvent [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM α' β') (ev : AnticipatedRNDEventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : AnticipatedRNDEvent v AM M α β α' β' :=
  {
    to_NDEvent := ev.to_NDEvent
    po := {
      safety := ev.safety
      feasibility := ev.feasibility
      lift_in := ev.lift_in
      lift_out := ev.lift_out
      abstract := abs.to_NDEvent
      strengthening := ev.strengthening
      simulation := ev.simulation
      variant := ev.variant
      nonIncreasing := ev.nonIncreasing
    }
  }

@[simp]
def newAnticipatedRNDEventfromOrdinary [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM α' β') (ev : AnticipatedRNDEventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : AnticipatedRNDEvent v AM M α β α' β' :=
  _newAnticipatedRNDEvent abs ev

@[simp]
def newAnticipatedRNDEventfromAnticipated [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : AnticipatedNDEvent v AM α' β') (ev : AnticipatedRNDEventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs.toOrdinaryNDEvent) : AnticipatedRNDEvent v AM M α β α' β' :=
  _newAnticipatedRNDEvent abs.toOrdinaryNDEvent ev

structure AnticipatedRNDEventSpec' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  {α α'} (abs : OrdinaryNDEvent AM α' Unit)
  extends _Variant v, RNDEventSpec' AM M (α:=α) (α':=α') abs where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ m', effect m x m'
            → variant m' ≤ variant m

@[simp]
def AnticipatedRNDEventSpec'.toAnticipatedRNDEventSpec [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM α' Unit)
  (ev : AnticipatedRNDEventSpec' v AM M (α:=α) (α':=α') abs): AnticipatedRNDEventSpec v AM M (α:=α) (β:=Unit) (α':=α') (β':=Unit) abs :=
  {
    toRNDEventSpec := ev.toRNDEventSpec
    variant := ev.variant
    nonIncreasing:= fun m x => by simp ; apply ev.nonIncreasing
  }

@[simp]
def newAnticipatedRNDEventfromOrdinary' [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM α' Unit) (ev : AnticipatedRNDEventSpec' v AM M (α:=α) (α':=α') abs) : AnticipatedRNDEvent v AM M α Unit α' Unit :=
  _newAnticipatedRNDEvent abs ev.toAnticipatedRNDEventSpec

@[simp]
def newAnticipatedRNDEventfromAnticipated' [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : AnticipatedNDEvent v AM α' Unit) (ev : AnticipatedRNDEventSpec' v AM M (α:=α) (α':=α') abs.toOrdinaryNDEvent) : AnticipatedRNDEvent v AM M α Unit α' Unit :=
  _newAnticipatedRNDEvent abs.toOrdinaryNDEvent ev.toAnticipatedRNDEventSpec

structure AnticipatedRNDEventSpec'' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit)
  extends _Variant v, RNDEventSpec'' AM M abs where

  nonIncreasing (m : M):
    Machine.invariant m
    → guard m
    → ∀ m', effect m m'
            → variant m' ≤ variant m

@[simp]
def AnticipatedRNDEventSpec''.toAnticipatedRNDEventSpec [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit)
  (ev : AnticipatedRNDEventSpec'' v AM M abs): AnticipatedRNDEventSpec v AM M (α:=Unit) (β:=Unit) (α':=Unit) (β':=Unit) abs :=
  {
    toRNDEventSpec := ev.toRNDEventSpec
    variant := ev.variant
    nonIncreasing:= fun m x => by simp ; apply ev.nonIncreasing
  }

@[simp]
def newAnticipatedRNDEventfromOrdinary'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit) (ev : AnticipatedRNDEventSpec'' v AM M abs) : AnticipatedRNDEvent v AM M Unit Unit :=
  _newAnticipatedRNDEvent abs ev.toAnticipatedRNDEventSpec

@[simp]
def newAnticipatedRNDEventfromAnticipated'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : AnticipatedNDEvent v AM Unit Unit) (ev : AnticipatedRNDEventSpec'' v AM M abs.toOrdinaryNDEvent) : AnticipatedRNDEvent v AM M Unit Unit :=
  _newAnticipatedRNDEvent abs.toOrdinaryNDEvent ev.toAnticipatedRNDEventSpec

structure _ConvergentRNDEventPO (v) [Preorder v] [WellFoundedLT v]  [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : _NDEvent M α β) (kind : EventKind) (α') (β')
          extends _Variant v, _AnticipatedRNDEventPO (instR:=instR) v ev kind α' β' where

  convergence (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → ∀ y, ∀ m', ev.effect m x (y, m')
                → variant m' < variant m

structure ConvergentRNDEvent (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  (α β) (α':=α) (β':=β)
  extends _NDEvent M α β where
  po : _ConvergentRNDEventPO v (instR:=instR) to_NDEvent (EventKind.TransDet Convergence.Anticipated) α' β'

@[simp]
def ConvergentRNDEvent.toConvergentNDEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : ConvergentRNDEvent v AM M α β α' β') : ConvergentNDEvent v M α β :=
  { to_NDEvent := ev.to_NDEvent
    po := {
      safety := ev.po.safety
      feasibility := ev.po.feasibility
      variant := ev.po.variant
      nonIncreasing := fun m x => by
        simp
        intros Hinv Hgrd y m' Heff
        have Hcv := ev.po.convergence m x Hinv Hgrd y m' Heff
        exact le_of_lt Hcv

      convergence := ev.po.convergence
    }
  }

structure ConvergentRNDEventSpec (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  {α β α' β'} (abs : OrdinaryNDEvent AM α' β')
  extends _Variant v, RNDEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs where

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ y, ∀ m', effect m x (y, m')
                 → variant m' < variant m

@[simp]
def newConvergentRNDEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM α' β') (ev : ConvergentRNDEventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : ConvergentRNDEvent v AM M α β α' β' :=
  {
    to_NDEvent := ev.to_NDEvent
    po := {
      safety := ev.safety
      feasibility := ev.feasibility
      abstract := abs.to_NDEvent
      strengthening := ev.strengthening
      simulation := ev.simulation
      variant := ev.variant
      nonIncreasing := fun m x => by
        simp
        intros Hinv Hgrd y m' Heff
        have Hcnv := ev.convergence m x Hinv Hgrd y m' Heff
        apply le_of_lt ; assumption
      convergence := ev.convergence
    }
  }

structure ConvergentRNDEventSpec' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  {α α'} (abs : OrdinaryNDEvent AM α' Unit)
  extends _Variant v, RNDEventSpec' AM M (α:=α) (α':=α') abs where

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ m', effect m x m'
            → variant m' < variant m

@[simp]
def ConvergentRNDEventSpec'.toConvergentRNDEventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM α' Unit)
  (ev : ConvergentRNDEventSpec' v AM M (α:=α) (α':=α') abs): ConvergentRNDEventSpec v AM M (α:=α) (β:=Unit) (α':=α') (β':=Unit) abs :=
  {
    toRNDEventSpec := ev.toRNDEventSpec
    variant := ev.variant
    convergence:= fun m x => by simp ; apply ev.convergence
  }

@[simp]
def newConvergentRNDEvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM α' Unit) (ev : ConvergentRNDEventSpec' v AM M (α:=α) (α':=α') abs) : ConvergentRNDEvent v AM M α Unit α' Unit :=
  newConvergentRNDEvent abs ev.toConvergentRNDEventSpec

structure ConvergentRNDEventSpec'' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit)
  extends _Variant v, RNDEventSpec'' AM M abs where

  convergence (m : M):
    Machine.invariant m
    → guard m
    → ∀ m', effect m m'
            → variant m' < variant m

@[simp]
def ConvergentRNDEventSpec''.toConvergentRNDEventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit)
  (ev : ConvergentRNDEventSpec'' v AM M abs): ConvergentRNDEventSpec v AM M (α:=Unit) (β:=Unit) (α':=Unit) (β':=Unit) abs :=
  {
    toRNDEventSpec := ev.toRNDEventSpec
    variant := ev.variant
    convergence:= fun m x => by simp ; apply ev.convergence
  }

@[simp]
def newConvergentRNDEvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit) (ev : ConvergentRNDEventSpec'' v AM M abs) : ConvergentRNDEvent v AM M Unit Unit :=
  newConvergentRNDEvent abs ev.toConvergentRNDEventSpec
