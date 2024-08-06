
import LeanMachines.Refinement.Relational.Basic
import LeanMachines.Event.Convergent

open Refinement

structure _AnticipatedREventPO (v) [Preorder v]  [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : _Event M α β) (kind : EventKind) (α') (β')
          extends _Variant v, _REventPO (instR:=instR) ev kind α' β'  where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → let (_, m') := ev.action m x
      variant m' ≤ variant m

structure AnticipatedREvent (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  (α β) (α':=α) (β':=β)
  extends _Event M α β where
  po : _AnticipatedREventPO v (instR:=instR) to_Event (EventKind.TransDet Convergence.Anticipated) α' β'

@[simp]
def AnticipatedREvent.toAnticipatedEvent [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : AnticipatedREvent v AM M α β α' β') : AnticipatedEvent v M α β :=
  { to_Event := ev.to_Event
    po := {
      to_EventPO := ev.po.to_EventPO
      variant := ev.po.variant
      nonIncreasing := ev.po.nonIncreasing
    } }

structure AnticipatedREventSpec (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  {α β α' β'} (abs : OrdinaryEvent AM α' β')
  extends _Variant v, REventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := (action m x).2
      variant m' ≤ variant m

@[simp]
private def _newAnticipatedREvent [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM α' β') (ev : AnticipatedREventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : AnticipatedREvent v AM M α β α' β' :=
  {
    to_Event := ev.to_Event
    po := {
      safety := ev.safety
      lift_in := ev.lift_in
      lift_out := ev.lift_out
      abstract := abs.to_Event
      strengthening := ev.strengthening
      simulation := ev.simulation
      variant := ev.variant
      nonIncreasing := ev.nonIncreasing
    }
  }

@[simp]
def newAnticipatedREventfromOrdinary [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM α' β') (ev : AnticipatedREventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : AnticipatedREvent v AM M α β α' β' :=
  _newAnticipatedREvent abs ev

@[simp]
def newAnticipatedREventfromAnticipated [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : AnticipatedEvent v AM α' β') (ev : AnticipatedREventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs.toOrdinaryEvent) : AnticipatedREvent v AM M α β α' β' :=
  _newAnticipatedREvent abs.toOrdinaryEvent ev

structure AnticipatedREventSpec' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  {α α'} (abs : OrdinaryEvent AM α' Unit)
  extends _Variant v, REventSpec' AM M (α:=α) (α':=α') abs where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := action m x
      variant m' ≤ variant m

@[simp]
def AnticipatedREventSpec'.toAnticipatedREventSpec [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM α' Unit) (ev : AnticipatedREventSpec' v AM M (α:=α) (α':=α') abs) : AnticipatedREventSpec v AM M (α:=α) (β:=Unit) (α':=α') (β':=Unit) abs :=
  {
    toREventSpec := ev.toREventSpec abs
    variant := ev.variant
    nonIncreasing := ev.nonIncreasing
  }

@[simp]
private def _newAnticipatedREvent' [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM α' Unit) (ev : AnticipatedREventSpec' v AM M (α:=α) (α':=α') abs) : AnticipatedREvent v AM M α Unit α' Unit :=
  _newAnticipatedREvent abs ev.toAnticipatedREventSpec

@[simp]
def newAnticipatedREventfromOrdinary' [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM α' Unit) (ev : AnticipatedREventSpec' v AM M (α:=α) (α':=α') abs) : AnticipatedREvent v AM M α Unit α' Unit :=
  _newAnticipatedREvent' abs ev

@[simp]
def newAnticipatedREventfromAnticipated' [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : AnticipatedEvent v AM α' Unit) (ev : AnticipatedREventSpec' v AM M (α:=α) (α':=α') abs.toOrdinaryEvent) : AnticipatedREvent v AM M α Unit α' Unit :=
  _newAnticipatedREvent' abs.toOrdinaryEvent ev

structure AnticipatedREventSpec'' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM Unit Unit)
  extends _Variant v, REventSpec'' AM M abs where

  nonIncreasing (m : M):
    Machine.invariant m
    → guard m
    → let m' := action m
      variant m' ≤ variant m

@[simp]
def AnticipatedREventSpec''.toAnticipatedREventSpec [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM Unit Unit) (ev : AnticipatedREventSpec'' v AM M abs) : AnticipatedREventSpec v AM M (α:=Unit) (β:=Unit) (α':=Unit) (β':=Unit) abs :=
  {
    toREventSpec := ev.toREventSpec abs
    variant := ev.variant
    nonIncreasing := fun m => by simp ; apply ev.nonIncreasing
  }

@[simp]
private def _newAnticipatedREvent'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM Unit Unit) (ev : AnticipatedREventSpec'' v AM M abs) : AnticipatedREvent v AM M Unit Unit :=
  _newAnticipatedREvent abs ev.toAnticipatedREventSpec

@[simp]
def newAnticipatedREventfromOrdinary'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM Unit Unit) (ev : AnticipatedREventSpec'' v AM M abs) : AnticipatedREvent v AM M Unit Unit :=
  _newAnticipatedREvent'' abs ev

@[simp]
def newAnticipatedREventfromAnticipated'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : AnticipatedEvent v AM Unit Unit) (ev : AnticipatedREventSpec'' v AM M abs.toOrdinaryEvent) : AnticipatedREvent v AM M Unit Unit :=
  _newAnticipatedREvent'' abs.toOrdinaryEvent ev

structure _ConvergentREventPO (v) [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : _Event M α β) (kind : EventKind) (α') (β')
  extends _AnticipatedREventPO (instR:=instR) v ev kind α' β' where

  convergence (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → let (_, m') := ev.action m x
      variant m' < variant m

structure ConvergentREvent (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  (α β) (α':=α) (β':=β)
  extends _Event M α β where
  po : _ConvergentREventPO v (instR:=instR) to_Event (EventKind.TransDet Convergence.Convergent) α' β'

@[simp]
def ConvergentREvent.toConvergentEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : ConvergentREvent v AM M α β α' β') : ConvergentEvent v M α β :=
  { to_Event := ev.to_Event
    po := {
      safety := ev.po.safety
      variant := ev.po.variant
      nonIncreasing := ev.po.nonIncreasing
      convergence := ev.po.convergence
    }
  }

structure ConvergentREventSpec (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  {α β α' β'} (abs : OrdinaryEvent AM α' β')
  extends _Variant v, REventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs where

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := (action m x).2
      variant m' < variant m

@[simp]
def newConvergentREvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM α' β') (ev : ConvergentREventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : ConvergentREvent v AM M α β α' β':=
  {
    guard := ev.guard
    action := ev.action
    po := {
      safety := ev.safety
      lift_in := ev.lift_in
      lift_out := ev.lift_out
      abstract := abs.to_Event
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

structure ConvergentREventSpec' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  {α α'} (abs : OrdinaryEvent AM α' Unit)
  extends _Variant v, REventSpec' AM M (α:=α) (α':=α') abs where

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := action m x
      variant m' < variant m

@[simp]
def ConvergentREventSpec'.toConvergentREventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM α' Unit) (ev : ConvergentREventSpec' v AM M (α:=α) (α':=α') abs) : ConvergentREventSpec v AM M (α:=α) (β:=Unit) (α':=α') (β':=Unit) abs :=
  {
    toREventSpec := ev.toREventSpec abs
    variant := ev.variant
    convergence := ev.convergence
  }

@[simp]
def newConvergentREvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM α' Unit) (ev : ConvergentREventSpec' v AM M (α:=α) (α':=α') abs) : ConvergentREvent v AM M α Unit α' Unit :=
  newConvergentREvent abs ev.toConvergentREventSpec

structure ConvergentREventSpec'' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM Unit Unit)
  extends _Variant v, REventSpec'' AM M abs where

  convergence (m : M):
    Machine.invariant m
    → guard m
    → let m' := action m
      variant m' < variant m

@[simp]
def ConvergentREventSpec''.toConvergentREventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM Unit Unit) (ev : ConvergentREventSpec'' v AM M abs) : ConvergentREventSpec v AM M (α:=Unit) (β:=Unit) (α':=Unit) (β':=Unit) abs :=
  {
    toREventSpec := ev.toREventSpec abs
    variant := ev.variant
    convergence := fun m () => ev.convergence m
  }

@[simp]
def newConvergentREvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM Unit Unit) (ev : ConvergentREventSpec'' v AM M abs) : ConvergentREvent v AM M Unit Unit :=
  newConvergentREvent abs ev.toConvergentREventSpec