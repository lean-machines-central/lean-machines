
import LeanMachines.Event.Basic
import LeanMachines.Refinement.Relational.Basic

/-!

# Functional refinement

This module contains the basic definitions of the functional
refinement principles for LeanMachines.
-/

/-!
## Machine refinement
-/

/-- The typeclass definition for the functional refinement
of an abstract machine type `AM` (in context `ACTX`) by
 a (more) concrete machine type `M` (in context `CTX`).
-/
class FRefinement {ACTX : outParam (Type u₁)} (AM)
                  {CTX : outParam (Type u₂)} (M)
                  [Machine ACTX AM] [Machine CTX M] where
  /-- The *lifting* of a concrete state `m` to the abstract level. -/
  lift (m : M): AM

  /-- The safety requirement of the `FRefinement.lift` method. -/
  lift_safe (m : M):
    Machine.invariant m
    → Machine.invariant (lift m)

open Refinement
open FRefinement

/--
The (somewhat meta-theoretical) proof that functional refinement is preserving
the relational `Refinement` principles. Technically, any (typeclass) instance
of a `FRefinement` is also an instance of `Refinement`.
-/
instance [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]: Refinement AM M where
  refine (am : AM) (m : M) := am = lift m

  refine_safe (am : AM) (m : M) := by
    simp
    intros Hinv Ham
    rw [Ham]
    exact lift_safe m Hinv

/-- This theorem allows to go back to the relational refinement level if needed. -/
theorem lift_ref [Machine ACTX AM] [Machine CTX M] [instFR:FRefinement AM M] (m : M) :
  Machine.invariant m
  → refine (AM:=AM) (self:=instRefinementOfFRefinement) (lift m) m :=
by
  simp [refine]

/-!

## Event refinement

For functional refinement, the event specifications are prefixed with by `FR`.

cf. the module `Refinement.Refinement.Basic` for further documentation.

-/

/-- Specification of ordinary refined events.
cf.  `REventSpec` in relational refinement.
 -/
structure FREventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [instfr: FRefinement AM M]
  {α β α' β'} (abstract : OrdinaryEvent AM α' β')
  extends EventSpec M α β where

  lift_in : α → α'
  lift_out : β → β'

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → abstract.guard (lift m) (lift_in x)

  simulation (m : M) (x : α):
    (Hinv : Machine.invariant m)
    → (Hgrd : guard m x)
    → let (y, m') := action m x Hgrd
      let (z, am') := abstract.action (lift m) (lift_in x) (strengthening m x Hinv Hgrd)
      lift_out y = z ∧ am' = (lift m')


@[simp]
def FREventSpec.toREventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  {α β α' β'} (abs : OrdinaryEvent AM α' β')
  (ev : FREventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : REventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs :=
  {
    toEventSpec := ev.toEventSpec

    lift_in := ev.lift_in
    lift_out := ev.lift_out

    strengthening := fun m x => by
      intros Hinv Hgrd am Href
      have Hst := ev.strengthening m x Hinv Hgrd
      simp [refine] at Href
      rw [Href]
      assumption

    simulation := fun m x => by
      simp
      intros Hinv Hgrd am Href
      have Hsim := ev.simulation m x Hinv Hgrd
      simp at Hsim
      simp [refine] at Href
      simp [Href]
      exact Hsim
  }

@[simp]
def newFREvent [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM α' β') (ev : FREventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : OrdinaryREvent AM M α β α' β' :=
  newREvent abs ev.toREventSpec

structure FREventSpec' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instfr: FRefinement AM M]
  {α α'} (abstract : OrdinaryEvent AM α' Unit)
  extends EventSpec' M α where

  lift_in : α → α'

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → abstract.guard (lift m) (lift_in x)

  simulation (m : M) (x : α):
    (Hinv : Machine.invariant m)
    → (Hgrd : guard m x)
    → let m' := action m x Hgrd
      let ((), am') := abstract.action (lift m) (lift_in x) (strengthening m x Hinv Hgrd)
      am' = (lift m')

@[simp]
def FREventSpec'.toFREventSpec [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  {α α'} (abs : OrdinaryEvent AM α' Unit)
  (ev : FREventSpec' AM M (α:=α) (α':=α') abs) : FREventSpec AM M (α:=α) (β:=Unit) (α':=α') (β':=Unit) abs :=
  {
    toEventSpec := ev.toEventSpec
    lift_in := ev.lift_in
    lift_out := id
    strengthening := ev.strengthening
    simulation := fun m x => by simp ; apply ev.simulation
  }

@[simp]
def newFREvent' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM α' Unit) (ev : FREventSpec' AM M (α:=α) (α':=α') abs) : OrdinaryREvent AM M α Unit α' Unit :=
  newFREvent abs ev.toFREventSpec

structure FREventSpec'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instfr: FRefinement AM M]
  (abstract : OrdinaryEvent AM Unit Unit)
  extends EventSpec'' M where

  strengthening (m : M):
    Machine.invariant m
    → guard m
    → abstract.guard (lift m) ()

  simulation (m : M):
    (Hinv : Machine.invariant m)
    → (Hgrd : guard m)
    → let m' := action m Hgrd
      let ((), am') := abstract.action (lift m) () (strengthening m Hinv Hgrd)
      am' = (lift m')

@[simp]
def FREventSpec''.toFREventSpec [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM Unit Unit)
  (ev : FREventSpec'' AM M abs) : FREventSpec AM M (α:=Unit) (β:=Unit) (α':=Unit) (β':=Unit) abs :=
  {
    toEventSpec := ev.toEventSpec
    lift_in := id
    lift_out := id
    strengthening := fun m () => ev.strengthening m
    simulation := fun m () => by
      simp
      intros Hinv Hgrd
      apply ev.simulation ; assumption
  }

@[simp]
def newFREvent'' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM Unit Unit) (ev : FREventSpec'' AM M abs) : OrdinaryREvent AM M Unit Unit :=
  newFREvent abs ev.toFREventSpec


/- Initialization events -/

structure InitFREventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [instFR: FRefinement AM M]
  {α β α' β'} (abstract : InitEvent AM α' β')
  extends InitEventSpec M α β where

  lift_in : α → α'
  lift_out : β → β'

  strengthening (x : α):
    guard x
    → abstract.guard (lift_in x)

  simulation (x : α):
    (Hgrd : guard x)
    → let (y, m') := init x Hgrd
      let (z, am') := abstract.init (lift_in x) (strengthening x Hgrd)
      lift_out y = z ∧ am' = lift m'

@[simp]
def InitFREventSpec.toInitREventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  {abs : InitEvent AM α' β'}
  (ev : InitFREventSpec (AM:=AM) (M:=M) (instFR:=instFR) (α:=α) (β:=β) (α':=α') (β':=β') abs)
    : InitREventSpec (AM:=AM) (M:=M) (α:=α) (β:=β) (α':=α') (β':=β') abs :=
  {
    toInitEventSpec := ev.toInitEventSpec
    lift_in := ev.lift_in
    lift_out := ev.lift_out
    strengthening := ev.strengthening
    simulation := fun x => by
      simp
      intro Hgrd
      have Hsim := ev.simulation x Hgrd
      simp at Hsim
      simp [Hsim]
      apply lift_ref
      apply ev.safety
  }

@[simp]
def newInitFREvent [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : InitEvent AM α' β') (ev : InitFREventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : InitREvent AM M α β α' β' :=
  newInitREvent abs ev.toInitREventSpec

structure InitFREventSpec' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instFR: FRefinement AM M]
  {α α'} (abstract : InitEvent AM α' Unit)
  extends InitEventSpec' M α where

  lift_in : α → α'

  strengthening (x : α):
    guard x
    → abstract.guard (lift_in x)

  simulation (x : α):
    (Hgrd : guard x)
    → let m' := init x Hgrd
      let ((), am') := abstract.init (lift_in x) (strengthening x Hgrd)
      am' = lift m'

@[simp]
def InitFREventSpec'.toInitFREventSpec [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  {α α'} (abs : InitEvent AM α' Unit)
  (ev : InitFREventSpec' AM M (α:=α) (α':=α') abs) : InitFREventSpec AM M (α:=α) (β:=Unit) (α':=α') (β':=Unit) abs :=
  {
    toInitEventSpec := ev.toInitEventSpec
    lift_in := ev.lift_in
    lift_out := id
    strengthening := ev.strengthening
    simulation := fun x => by
      simp
      intros Hgrd
      apply ev.simulation
  }

@[simp]
def newInitFREvent' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : InitEvent AM α' Unit) (ev : InitFREventSpec' AM M (α:=α) (α':=α') abs) : InitREvent AM M α Unit α' Unit :=
  newInitFREvent abs ev.toInitFREventSpec

structure InitFREventSpec'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instFR: FRefinement AM M]
  (abstract : InitEvent AM Unit Unit)
  extends InitEventSpec'' M where

  strengthening:
    guard
    → abstract.guard ()

  simulation:
    (Hgrd : guard)
    → let m' := init Hgrd
      let ((), am') := abstract.init () (strengthening Hgrd)
      am' = lift m'

@[simp]
def InitFREventSpec''.toInitFREventSpec [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : InitEvent AM Unit Unit)
  (ev : InitFREventSpec'' AM M abs) : InitFREventSpec AM M (α:=Unit) (β:=Unit) (α':=Unit) (β':=Unit) abs :=
  {
    toInitEventSpec := ev.toInitEventSpec
    lift_in := id
    lift_out := id
    strengthening := fun () => ev.strengthening
    simulation := fun () => by
      simp
      intros Hgrd
      apply ev.simulation
  }

@[simp]
def newInitFREvent'' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : InitEvent AM Unit Unit) (ev : InitFREventSpec'' AM M abs) : InitREvent AM M Unit Unit :=
  newInitFREvent abs ev.toInitFREventSpec
