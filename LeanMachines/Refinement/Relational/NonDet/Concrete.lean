

import LeanMachines.NonDet.Basic
import LeanMachines.NonDet.Ordinary

import LeanMachines.Refinement.Relational.Basic
import LeanMachines.Refinement.Relational.NonDet.Convergent

/-!

# Defining new, concrete non-deterministic events

Concrete events are events only available at the concrete level
when defining a refined machine.

This module implements the non-deterministic case, cf.
 `Refinement.Relational.Concrete` for further information and
 the deterministic case.

-/

open Refinement

/-!
## Concrete ordinary events
-/

/-- The specification of a concrete (ordinary) non-deterministic event, refining (non-deterministic) Skip.-/
structure ConcreteRNDEvent (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M] (α) (β)
  extends OrdinaryNDEvent M α β where

  /-- Proof obligation: the refined event safely simulates the non-deterministic Skip event
   (no state change at the abstract level). -/
  simulation (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ y, ∀ m', effect m x grd (y, m')
                   → ∀ am, refine am m
                           → refine (self:=instR) am m'

/-- The construction of a concrete (ordinary) non-deterministic event
 from a `ConcreteRNDEventSpec` specification. -/
@[simp]
def newConcreteRNDEvent [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : ConcreteRNDEvent AM M α β) : OrdinaryRNDEvent AM M α β Unit Unit skip_NDEvent :=
  {
    guard := ev.guard
    effect := ev.effect
    safety := ev.safety
    feasibility := ev.feasibility
    lift_in := fun _ => ()
    lift_out := fun _ => ()
    strengthening _ _ _ _ _ _ := trivial
    simulation m x := by
      simp only [skip_NDEvent, exists_eq_left]
      apply ev.simulation
  }

/-- Variant of `ConcreteRNDEventSpec` with implicit `Unit` output type -/
structure ConcreteRNDEvent' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M] (α)
  extends OrdinaryNDEvent' M α where

  simulation (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ m', effect m x grd m'
            → ∀ am, refine am m
                    → refine (self:=instR) am m'

instance [Machine CTX M] [Machine ACTX AM] [Refinement AM M] :
  Coe (ConcreteRNDEvent' AM M α) (ConcreteRNDEvent  AM M  α Unit) where
  coe ev := {
              simulation m x hinv grd _ m' := ev.simulation m x hinv grd m'
              guard := ev.guard
              effect m x grd ym' := ev.effect m x grd ym'.2
              safety m x hinv hgrd _ m' := ev.safety m x hinv hgrd m'
              feasibility m x hinv grd := ⟨(), ev.feasibility m x hinv grd⟩
            }

/-- Variant of `newConcreteRNDEvent` with implicit `Unit` output type -/

@[simp]
def newConcreteRNDEvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : ConcreteRNDEvent' AM M α) : OrdinaryRNDEvent AM M α Unit Unit Unit skip_NDEvent :=
  newConcreteRNDEvent ev

/-- Variant of `ConcreteRNDEventSpec` with implicit `Unit` input and output types -/
structure ConcreteRNDEvent'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  extends OrdinaryNDEvent'' M where

  simulation (m : M):
    Machine.invariant m
    → (grd : guard m)
    → ∀ m', effect m grd m'
            → ∀ am, refine am m
                    → refine (self:=instR) am m'

instance [Machine CTX M] [Machine ACTX AM] [Refinement AM M] :
  Coe (ConcreteRNDEvent'' AM M ) (ConcreteRNDEvent  AM M  Unit Unit) where
  coe ev := {
              simulation m _ hinv grd _ m' := ev.simulation m  hinv grd m'
              guard m _ := ev.guard m
              effect m _ grd ym' := ev.effect m  grd ym'.2
              safety m _ hinv hgrd _ m' := ev.safety m  hinv hgrd m'
              feasibility m _ hinv grd := ⟨(), ev.feasibility m hinv grd⟩
            }

/-- Variant of `newConcreteRNDEvent` with implicit `Unit` input and output types -/
@[simp]
def newConcreteNDEvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : ConcreteRNDEvent'' AM M) : OrdinaryRNDEvent AM M Unit Unit Unit Unit skip_NDEvent :=
  newConcreteRNDEvent ev

/-!
## Concrete anticipated events

**Remark**:  for Event-B (conceptual) compatibility, this is the minimal set of requirements
for introducing new, concrete events in a refined machine.
-/

/-- The specification of a concrete non-deterministic anticipated event, with the requirements
of `ConcreteRNDEventSpec` together with anticipation requirements (variant, etc).-/
structure ConcreteAnticipatedRNDEvent (v) [Preorder v] [WellFoundedLT v] (AM)
   [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M] (α) (β)
  extends ConcreteRNDEvent AM M α β where

  variant : M → v
  /-- Proof obligation: the concrete variant does not increases. -/
  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ y, ∀ m', effect m x grd (y, m')
                 → variant m' ≤ variant m

/-- The construction of a concrete non-deterministic anticipated event
from a `ConcreteAnticipatedRNDEventSpec` specification. -/
@[simp]
def newConcreteAnticipatedRNDEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : ConcreteAnticipatedRNDEvent v AM M α β) : AnticipatedRNDEvent v AM M α β Unit Unit skip_NDEvent :=
  {
    guard := ev.guard
    effect := ev.effect
    safety := ev.safety
    feasibility := ev.feasibility
    variant := ev.variant
    nonIncreasing m x  Hinv Hgrd y m' Heff := ev.nonIncreasing m x Hinv Hgrd y m' Heff
    lift_in := fun _ => ()
    lift_out := fun _ => ()
    strengthening _ _ _ _ _ _ := trivial
    simulation m x := by simp only [skip_NDEvent, exists_eq_left] ; apply ev.simulation
  }

/-- Variant of `ConcreteAnticipatedRNDEventSpec` with implicit `Unit` output type -/
structure ConcreteAnticipatedRNDEvent' (v) [Preorder v] [WellFoundedLT v] (AM)
  [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M] (α)
  extends  ConcreteRNDEvent' AM M α where
  variant : M → v

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ m', effect m x grd m'
            → variant m' ≤ variant m


instance [Machine CTX M] [Machine ACTX AM] [Refinement AM M]
  [Preorder v] [WellFoundedLT v]  :
  Coe (ConcreteAnticipatedRNDEvent' v AM M α) (ConcreteAnticipatedRNDEvent v AM M α Unit) where
  coe ev := {
              simulation m x hinv grd _ m' := ev.simulation m  x hinv grd m'
              guard := ev.guard
              effect m x grd ym' := ev.effect m x grd ym'.2
              safety m x hinv hgrd _ m' := ev.safety m x hinv hgrd m'
              feasibility m x hinv grd := ⟨(), ev.feasibility m x hinv grd⟩
              variant := ev.variant
              nonIncreasing m x := by simp only [forall_const] ; apply ev.nonIncreasing
            }

/-- Variant of `newConcreteAnticipatedRNDEvent` with implicit `Unit` output type -/
@[simp]
def newConcreteAnticipatedRNDEvent' [Preorder v] [WellFoundedLT v]
  [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : ConcreteAnticipatedRNDEvent' v AM M α) : AnticipatedRNDEvent v AM M α Unit Unit Unit skip_NDEvent:=
  newConcreteAnticipatedRNDEvent ev

/-- Variant of `ConcreteAnticipatedRNDEventSpec` with implicit `Unit` input and output types -/
structure ConcreteAnticipatedRNDEvent'' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  extends ConcreteRNDEvent'' AM M where

  variant : M → v
  nonIncreasing (m : M):
    Machine.invariant m
    → (grd : guard m)
    → ∀ m', effect m grd m'
            → variant m' ≤ variant m

instance [Machine CTX M] [Machine ACTX AM] [Refinement AM M]
  [Preorder v] [WellFoundedLT v]  :
  Coe (ConcreteAnticipatedRNDEvent'' v AM M) (ConcreteAnticipatedRNDEvent v AM M Unit Unit) where
  coe ev := {
              simulation m x hinv grd _ m' := ev.simulation m hinv grd m'
              guard m _ := ev.guard m
              effect m _ grd ym' := ev.effect m grd ym'.2
              safety m _ hinv hgrd _ m' := ev.safety m hinv hgrd m'
              feasibility m _ hinv grd := ⟨(), ev.feasibility m hinv grd⟩
              variant := ev.variant
              nonIncreasing m _ := by simp only [forall_const] ; apply ev.nonIncreasing
            }

/-- Variant of `newConcreteAnticipatedRNDEvent` with implicit `Unit` input and output types -/
@[simp]
def newConcreteAnticipatedNDEvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : ConcreteAnticipatedRNDEvent'' v AM M)
  : AnticipatedRNDEvent v AM M Unit Unit Unit Unit skip_NDEvent:=
  newConcreteAnticipatedRNDEvent ev

/-!
## Concrete convergent events
-/

/-- The specification of a concrete non-deterministic convergent event, with the requirements
of `ConcreteRNDEventSpec` together with convergence requirements (variant, etc).-/
structure ConcreteConvergentRNDEvent (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M] (α) (β)
  extends ConcreteRNDEvent AM M α β where
  variant : M → v

  /-- Proof obligation: the variant strictly decrases. -/
  convergence (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ y, ∀ m', effect m x grd (y, m')
                 → variant m' < variant m

/-- The construction of a concrete non-deterministic convergent event
from a `ConcreteConvergentRNDEventSpec` specification. -/
@[simp]
def newConcreteConvergentRNDEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : ConcreteConvergentRNDEvent v AM M α β) : ConvergentRNDEvent v AM M α β Unit Unit skip_NDEvent :=
  {
    guard := ev.guard
    effect := ev.effect
    safety := ev.safety
    feasibility := ev.feasibility
    variant := ev.variant
    convergence := ev.convergence
    lift_in := fun _ => ()
    lift_out := fun _ => ()
    strengthening _ _ _ _ _ _:= trivial
    simulation m x := by simp only [skip_NDEvent, exists_eq_left] ; apply ev.simulation
  }

/-- Variant of `ConcreteConvergentRNDEventSpec` with implicit `Unit` output type -/
structure ConcreteConvergentRNDEvent' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M] (α)
  extends ConcreteRNDEvent' AM M α where
  variant : M → v

  convergence (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ m', effect m x grd m'
            → variant m' < variant m

instance [Machine CTX M] [Machine ACTX AM] [Refinement AM M]
  [Preorder v] [WellFoundedLT v]  :
  Coe (ConcreteConvergentRNDEvent' v AM M α) (ConcreteConvergentRNDEvent v AM M α Unit) where
  coe ev := {
              simulation m x hinv grd _ m' := ev.simulation m  x hinv grd m'
              guard := ev.guard
              effect m x grd ym' := ev.effect m x grd ym'.2
              safety m x hinv hgrd _ m' := ev.safety m x hinv hgrd m'
              feasibility m x hinv grd := ⟨(), ev.feasibility m x hinv grd⟩
              variant := ev.variant
              convergence m x := by simp only [forall_const] ; apply ev.convergence
            }


/-- Variant of `newConcreteConvergentRNDEvent` with implicit `Unit` output type -/
@[simp]
def newConcreteConvergentRNDEvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : ConcreteConvergentRNDEvent' v AM M α) :
    ConvergentRNDEvent v AM M α Unit Unit Unit skip_NDEvent :=
  newConcreteConvergentRNDEvent ev

/-- Variant of `ConcreteConvergentRNDEventSpec` with implicit `Unit` input and output types -/
structure ConcreteConvergentRNDEvent'' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  extends ConcreteRNDEvent'' AM M where
  variant : M → v

  convergence (m : M):
    Machine.invariant m
    → (grd : guard m)
    → ∀ m', effect m grd m'
            → variant m' < variant m

instance [Machine CTX M] [Machine ACTX AM] [Refinement AM M]
  [Preorder v] [WellFoundedLT v]  :
  Coe (ConcreteConvergentRNDEvent'' v AM M) (ConcreteConvergentRNDEvent v AM M Unit Unit) where
  coe ev := {
              simulation m x hinv grd _ m' := ev.simulation m hinv grd m'
              guard m _ := ev.guard m
              effect m _ grd ym' := ev.effect m grd ym'.2
              safety m _ hinv hgrd _ m' := ev.safety m hinv hgrd m'
              feasibility m _ hinv grd := ⟨(), ev.feasibility m hinv grd⟩
              variant := ev.variant
              convergence m _ := by simp only [forall_const] ; apply ev.convergence
            }

/-- Variant of `newConcreteConvergentRNDEvent` with implicit `Unit` input and output types -/
@[simp]
def newConcreteConvergentNDEvent'' [Preorder v] [WellFoundedLT v]
  [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (ev : ConcreteConvergentRNDEvent'' v AM M) :
  ConvergentRNDEvent v AM M Unit Unit Unit Unit skip_NDEvent := newConcreteConvergentRNDEvent ev
