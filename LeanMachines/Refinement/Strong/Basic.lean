
import LeanMachines.Refinement.Functional.Basic

/-!

# Strong (Functional) refinement

This module contains the basic definitions of the strong variant
of functional refinement. In this more constrained form of
refinement it is easier to reuse abstract events, even in the
case of non-trivial data refinement steps (if compatible with
the strong refinement requirements).
-/

/-!

## Machine refinement

-/

open Refinement
open FRefinement

/-!
## Machine refinement
-/

/-- The typeclass of strong functional refinement, which inherits from
the functional refinement requirements of typeclass `FRefinement`.
This introduces the notion of *unlifting* that corresponds to the
reconstruction of a concrete state after an abstract state change.
If this operation is possible then strong refinement is highly
recommended.

The requirements are similar to the one needed for the reuse of
abstract event in the case of relational refinement
(cf. module `Refinement.Relational.Abstract`).
However, the requirements are now promoted to the machine-level.
-/
class SRefinement {ACTX : outParam (Type u₁)} (AM)
                 {CTX : outParam (Type u₂)} (M)
                 [Machine ACTX AM] [Machine CTX M] extends FRefinement AM M where

  /-- Reconstruction of a concrete post-state from a concrete-pre state `m`
   and an abstract post-state `am'`.
   Note that the abstract pre-state is also available as `lift m`.
   -/
  unlift (m : M) (am' : AM): M

  /-- Proof obligation: lifting an unlifted abstract state change is invariant.
   A kind of a functionality requirement. -/
  lift_unlift (m : M) (am' : AM):
    Machine.invariant m → Machine.invariant am'
    → lift (unlift m am') = am'

  /-- Proof obligation: a special case of `lift_unlift` for the `reset` state. -/
  lu_reset (am' : AM):
    Machine.invariant am'
    → lift (unlift default am') = am'

open Refinement
open SRefinement

theorem unlift_refine [Machine ACTX AM] [Machine CTX M] [instSR:SRefinement AM M] {m : M} {am : AM}:
    Machine.invariant m → Machine.invariant am → refine am (unlift m am) := by
  intro Hinv₁ Hinv₂
  have Href: refine (self:=inferInstanceAs (Refinement AM M)) (lift (unlift m am)) (unlift m am) := rfl
  rw [lift_unlift] at Href <;> assumption

/-!
## Event refinement

The construction of refined events following the strong refinement principles
are quite similar to the functional ones, with the notable exception of reusing
abstract events (cf. `Refinement.Strong.Abstract`).

For strong refinement, the event specifications are prefixed with by `SR`.

cf. the module `Refinement.Functional.Basic` for further documentation.

-/

@[simp]
def newSREvent [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryEvent AM α' β') (ev : FREventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : OrdinaryREvent AM M α β α' β' :=
  newREvent abs ev.toREventSpec

@[simp]
def newSREvent' [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryEvent AM α' Unit) (ev : FREventSpec' AM M (α:=α) (α':=α') abs) : OrdinaryREvent AM M α Unit α' Unit :=
  newSREvent abs ev.toFREventSpec

@[simp]
def newSREvent'' [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryEvent AM Unit Unit) (ev : FREventSpec'' AM M abs) : OrdinaryREvent AM M Unit Unit :=
  newSREvent abs ev.toFREventSpec

/- Initialization events -/

@[simp]
def newInitSREvent [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : InitEvent AM α' β') (ev : InitFREventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : InitREvent AM M α β α' β' :=
  newInitREvent abs ev.toInitREventSpec

@[simp]
def newInitSREvent' [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : InitEvent AM α' Unit) (ev : InitFREventSpec' AM M (α:=α) (α':=α') abs) : InitREvent AM M α Unit α' Unit :=
  newInitSREvent abs ev.toInitFREventSpec

@[simp]
def newInitSREvent'' [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : InitEvent AM Unit Unit) (ev : InitFREventSpec'' AM M abs) : InitREvent AM M Unit Unit :=
  newInitSREvent abs ev.toInitFREventSpec
