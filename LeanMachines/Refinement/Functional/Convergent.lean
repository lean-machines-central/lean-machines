
import LeanMachines.Refinement.Functional.Basic
import LeanMachines.Refinement.Relational.Convergent
import LeanMachines.Event.Convergent

open Refinement
open FRefinement

structure AnticipatedFREventSpec (v) [Preorder v] (AM) [Machine ACTX AM] (M) [instM:Machine CTX M] [FRefinement AM M]
  {α β α' β'} (abs : OrdinaryEvent AM α' β')
  extends _Variant v (instM:=instM), FREventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := (action m x).2
      variant m' ≤ variant m

@[simp]
def AnticipatedFREventSpec.toAnticipatedREventSpec [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM α' β') (ev :  AnticipatedFREventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : AnticipatedREventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs :=
  {
    toREventSpec := ev.toREventSpec
    variant := ev.variant
    nonIncreasing := ev.nonIncreasing
  }

@[simp]
def newAnticipatedFREventfromOrdinary [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM α' β') (ev : AnticipatedFREventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : AnticipatedREvent v AM M α β α' β' :=
  newAnticipatedREventfromOrdinary abs ev.toAnticipatedREventSpec

structure AnticipatedFREventSpec' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [instM:Machine CTX M] [FRefinement AM M]
  {α α'} (abs : OrdinaryEvent AM α' Unit)
  extends _Variant v (instM:=instM), FREventSpec' AM M (α:=α) (α':=α') abs where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := action m x
      variant m' ≤ variant m

@[simp]
def AnticipatedFREventSpec'.toAnticipatedFREventSpec [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM α' Unit) (ev :  AnticipatedFREventSpec' v AM M (α:=α) (α':=α') abs) : AnticipatedFREventSpec v AM M (α:=α) (β:=Unit) (α':=α') (β':=Unit) abs :=
  {
    toFREventSpec := ev.toFREventSpec
    variant := ev.variant
    nonIncreasing := ev.nonIncreasing
  }

@[simp]
def newAnticipatedFREventfromOrdinary' [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM α' Unit) (ev : AnticipatedFREventSpec' v AM M (α:=α) (α':=α') abs) : AnticipatedREvent v AM M α Unit α' Unit :=
  newAnticipatedFREventfromOrdinary abs ev.toAnticipatedFREventSpec

structure AnticipatedFREventSpec'' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [instM:Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM Unit Unit)
  extends _Variant v (instM:=instM), FREventSpec'' AM M abs where

  nonIncreasing (m : M):
    Machine.invariant m
    → guard m
    → let m' := action m
      variant m' ≤ variant m

@[simp]
def AnticipatedFREventSpec''.toAnticipatedFREventSpec [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM Unit Unit) (ev :  AnticipatedFREventSpec'' v AM M abs) : AnticipatedFREventSpec v AM M (α:=Unit) (β:=Unit) (α':=Unit) (β':=Unit) abs :=
  {
    toFREventSpec := ev.toFREventSpec
    variant := ev.variant
    nonIncreasing := fun m _ => ev.nonIncreasing m
  }

@[simp]
def newAnticipatedFREventfromOrdinary'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM Unit Unit) (ev : AnticipatedFREventSpec'' v AM M abs) : AnticipatedREvent v AM M Unit Unit :=
  newAnticipatedFREventfromOrdinary abs ev.toAnticipatedFREventSpec

@[simp]
def newAnticipatedFREventfromAnticipated [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : AnticipatedEvent v AM α' β') (ev : AnticipatedFREventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs.toOrdinaryEvent) : AnticipatedREvent v AM M α β α' β' :=
  newAnticipatedREventfromAnticipated abs ev.toAnticipatedREventSpec

@[simp]
def newAnticipatedFREventfromAnticipated' [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : AnticipatedEvent v AM α' Unit) (ev : AnticipatedFREventSpec' v AM M (α:=α) (α':=α') abs.toOrdinaryEvent) : AnticipatedREvent v AM M α Unit α' Unit :=
  newAnticipatedFREventfromAnticipated abs ev.toAnticipatedFREventSpec

@[simp]
def newAnticipatedFREventfromAnticipated'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : AnticipatedEvent v AM Unit Unit) (ev : AnticipatedFREventSpec'' v AM M abs.toOrdinaryEvent) : AnticipatedREvent v AM M Unit Unit :=
  newAnticipatedFREventfromAnticipated abs ev.toAnticipatedFREventSpec

structure ConvergentFREventSpec (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [instM:Machine CTX M] [FRefinement AM M]
  {α β α' β'} (abs : OrdinaryEvent AM α' β')
  extends _Variant v (instM:=instM), FREventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs where

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := (action m x).2
      variant m' < variant m

@[simp]
def ConvergentFREventSpec.toConvergentREventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM α' β') (ev :  ConvergentFREventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : ConvergentREventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs :=
  {
    toREventSpec := ev.toREventSpec
    variant := ev.variant
    convergence := ev.convergence
  }

@[simp]
def newConvergentFREvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM α' β') (ev : ConvergentFREventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : ConvergentREvent v AM M α β α' β' :=
  newConvergentREvent abs ev.toConvergentREventSpec

structure ConvergentFREventSpec' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [instM:Machine CTX M] [FRefinement AM M]
  {α α'} (abs : OrdinaryEvent AM α' Unit)
  extends _Variant v (instM:=instM), FREventSpec' AM M (α:=α) (α':=α') abs where

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := action m x
      variant m' < variant m

@[simp]
def ConvergentFREventSpec'.toConvergentFREventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM α' Unit) (ev :  ConvergentFREventSpec' v AM M (α:=α) (α':=α') abs) : ConvergentFREventSpec v AM M (α:=α) (β:=Unit) (α':=α') (β':=Unit) abs :=
  {
    toFREventSpec := ev.toFREventSpec
    variant := ev.variant
    convergence := ev.convergence
  }

@[simp]
def newConvergentFREvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM α' Unit) (ev : ConvergentFREventSpec' v AM M (α:=α) (α':=α') abs) : ConvergentREvent v AM M α Unit α' Unit :=
  newConvergentFREvent abs ev.toConvergentFREventSpec

structure ConvergentFREventSpec'' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [instM:Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM Unit Unit)
  extends _Variant v (instM:=instM), FREventSpec'' AM M abs where

  convergence (m : M):
    Machine.invariant m
    → guard m
    → let m' := action m
      variant m' < variant m

@[simp]
def ConvergentFREventSpec''.toConvergentFREventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM Unit Unit) (ev :  ConvergentFREventSpec'' v AM M abs) : ConvergentFREventSpec v AM M (α:=Unit) (β:=Unit) (α':=Unit) (β':=Unit) abs :=
  {
    toFREventSpec := ev.toFREventSpec
    variant := ev.variant
    convergence := fun m () => ev.convergence m
  }

@[simp]
def newConvergentFREvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM Unit Unit) (ev : ConvergentFREventSpec'' v AM M abs) : ConvergentREvent v AM M Unit Unit :=
  newConvergentFREvent abs ev.toConvergentFREventSpec
