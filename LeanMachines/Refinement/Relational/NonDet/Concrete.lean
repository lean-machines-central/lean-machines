

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
structure ConcreteRNDEventSpec (AM) [@Machine ACTX AM] (M) [@Machine CTX M] [instR: Refinement AM M] (α) (β)
  extends NDEventSpec M α β where

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
def newConcreteRNDEvent [@Machine ACTX AM] [@Machine CTX M] [instR: Refinement AM M]
  (ev : ConcreteRNDEventSpec AM M α β) : OrdinaryRNDEvent AM M α β :=
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
    }
  }

/-- Variant of `ConcreteRNDEventSpec` with implicit `Unit` output type -/
structure ConcreteRNDEventSpec' (AM) [@Machine ACTX AM] (M) [@Machine CTX M] [instR: Refinement AM M] (α)
  extends NDEventSpec' M α where

  simulation (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ m', effect m x grd m'
            → ∀ am, refine am m
                    → refine (self:=instR) am m'

@[simp]
def ConcreteRNDEventSpec'.toConcreteRNDEventSpec [@Machine ACTX AM] [@Machine CTX M] [instR: Refinement AM M]
  (ev : ConcreteRNDEventSpec' AM M α) : ConcreteRNDEventSpec AM M α Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec
    simulation := fun m x => by simp ; apply ev.simulation
  }

/-- Variant of `newConcreteRNDEvent` with implicit `Unit` output type -/
@[simp]
def newConcreteRNDEvent' [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (ev : ConcreteRNDEventSpec' AM M α) : OrdinaryRNDEvent AM M α Unit :=
  newConcreteRNDEvent ev.toConcreteRNDEventSpec

/-- Variant of `ConcreteRNDEventSpec` with implicit `Unit` input and output types -/
structure ConcreteRNDEventSpec'' (AM) [@Machine ACTX AM] (M) [@Machine CTX M] [instR: Refinement AM M]
  extends NDEventSpec'' M where

  simulation (m : M):
    Machine.invariant m
    → (grd : guard m)
    → ∀ m', effect m grd m'
            → ∀ am, refine am m
                    → refine (self:=instR) am m'

@[simp]
def ConcreteRNDEventSpec''.toConcreteRNDEventSpec [@Machine ACTX AM] [@Machine CTX M] [instR: Refinement AM M]
  (ev : ConcreteRNDEventSpec'' AM M) : ConcreteRNDEventSpec AM M Unit Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec
    simulation := fun m grd => by simp ; apply ev.simulation
  }

/-- Variant of `newConcreteRNDEvent` with implicit `Unit` input and output types -/
@[simp]
def newConcreteNDEvent'' [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (ev : ConcreteRNDEventSpec'' AM M) : OrdinaryRNDEvent AM M Unit Unit :=
  newConcreteRNDEvent ev.toConcreteRNDEventSpec

/-!
## Concrete anticipated events

**Remark**:  for Event-B (conceptual) compatibility, this is the minimal set of requirements
for introducing new, concrete events in a refined machine.
-/

/-- The specification of a concrete non-deterministic anticipated event, with the requirements
of `ConcreteRNDEventSpec` together with anticipation requirements (variant, etc).-/
structure ConcreteAnticipatedRNDEventSpec (v) [Preorder v] [WellFoundedLT v] (AM) [@Machine ACTX AM] (M) [@Machine CTX M] [instR: Refinement AM M] (α) (β)
  extends _Variant v (M:=M), ConcreteRNDEventSpec AM M α β where

  /-- Proof obligation: the concrete variant does not increases. -/
  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ y, ∀ m', effect m x grd (y, m')
                 → variant m' ≤ variant m

/-- The construction of a concrete non-deterministic anticipated event
from a `ConcreteAnticipatedRNDEventSpec` specification. -/
@[simp]
def newConcreteAnticipatedRNDEvent [Preorder v] [WellFoundedLT v] [@Machine ACTX AM] [@Machine CTX M] [instR: Refinement AM M]
  (ev : ConcreteAnticipatedRNDEventSpec v AM M α β) : AnticipatedRNDEvent v AM M α β :=
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
      nonIncreasing := fun m x => by
        simp
        intros Hinv Hgrd y m' Heff
        exact ev.nonIncreasing m x Hinv Hgrd y m' Heff
    }
  }

/-- Variant of `ConcreteAnticipatedRNDEventSpec` with implicit `Unit` output type -/
structure ConcreteAnticipatedRNDEventSpec' (v) [Preorder v] [WellFoundedLT v] (AM) [@Machine ACTX AM] (M) [@Machine CTX M] [instR: Refinement AM M] (α)
  extends _Variant v (M:=M), ConcreteRNDEventSpec' AM M α where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ m', effect m x grd m'
            → variant m' ≤ variant m

@[simp]
def ConcreteAnticipatedRNDEventSpec'.toConcreteAnticipatedRNDEventSpec [Preorder v] [WellFoundedLT v] [@Machine ACTX AM] [@Machine CTX M] [instR: Refinement AM M]
  (ev : ConcreteAnticipatedRNDEventSpec' v AM M α) : ConcreteAnticipatedRNDEventSpec v AM M α Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec
    variant := ev.variant
    simulation := fun m x => by simp ; apply ev.simulation
    nonIncreasing := fun m x => by simp ; apply ev.nonIncreasing
  }

/-- Variant of `newConcreteAnticipatedRNDEvent` with implicit `Unit` output type -/
@[simp]
def newConcreteAnticipatedRNDEvent' [Preorder v] [WellFoundedLT v] [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (ev : ConcreteAnticipatedRNDEventSpec' v AM M α) : AnticipatedRNDEvent v AM M α Unit :=
  newConcreteAnticipatedRNDEvent ev.toConcreteAnticipatedRNDEventSpec

/-- Variant of `ConcreteAnticipatedRNDEventSpec` with implicit `Unit` input and output types -/
structure ConcreteAnticipatedRNDEventSpec'' (v) [Preorder v] [WellFoundedLT v] (AM) [@Machine ACTX AM] (M) [@Machine CTX M] [instR: Refinement AM M]
  extends _Variant v (M:=M), ConcreteRNDEventSpec'' AM M where

  nonIncreasing (m : M):
    Machine.invariant m
    → (grd : guard m)
    → ∀ m', effect m grd m'
            → variant m' ≤ variant m

@[simp]
def ConcreteAnticipatedRNDEventSpec''.toConcreteAnticipatedRNDEventSpec [Preorder v] [WellFoundedLT v] [@Machine ACTX AM] [@Machine CTX M] [instR: Refinement AM M]
  (ev : ConcreteAnticipatedRNDEventSpec'' v AM M) : ConcreteAnticipatedRNDEventSpec v AM M Unit Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec
    variant := ev.variant
    simulation := fun m grd => by simp ; apply ev.simulation
    nonIncreasing := fun m grd => by simp ; apply ev.nonIncreasing
  }

/-- Variant of `newConcreteAnticipatedRNDEvent` with implicit `Unit` input and output types -/
@[simp]
def newConcreteAnticipatedNDEvent'' [Preorder v] [WellFoundedLT v] [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (ev : ConcreteAnticipatedRNDEventSpec'' v AM M) : AnticipatedRNDEvent v AM M Unit Unit :=
  newConcreteAnticipatedRNDEvent ev.toConcreteAnticipatedRNDEventSpec

/-!
## Concrete convergent events
-/

/-- The specification of a concrete non-deterministic convergent event, with the requirements
of `ConcreteRNDEventSpec` together with convergence requirements (variant, etc).-/
structure ConcreteConvergentRNDEventSpec (v) [Preorder v] [WellFoundedLT v] (AM) [@Machine ACTX AM] (M) [@Machine CTX M] [instR: Refinement AM M] (α) (β)
  extends _Variant v (M:=M), ConcreteRNDEventSpec AM M α β where

  /-- Proof obligation: the variant strictly decrases. -/
  convergence (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ y, ∀ m', effect m x grd (y, m')
                 → variant m' < variant m

/-- The construction of a concrete non-deterministic convergent event
from a `ConcreteConvergentRNDEventSpec` specification. -/
@[simp]
def newConcreteConvergentRNDEvent [Preorder v] [WellFoundedLT v] [@Machine ACTX AM] [@Machine CTX M] [instR: Refinement AM M]
  (ev : ConcreteConvergentRNDEventSpec v AM M α β) : ConvergentRNDEvent v AM M α β :=
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

/-- Variant of `ConcreteConvergentRNDEventSpec` with implicit `Unit` output type -/
structure ConcreteConvergentRNDEventSpec' (v) [Preorder v] [WellFoundedLT v] (AM) [@Machine ACTX AM] (M) [@Machine CTX M] [instR: Refinement AM M] (α)
  extends _Variant v (M:=M), ConcreteRNDEventSpec' AM M α where

  convergence (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ m', effect m x grd m'
            → variant m' < variant m

@[simp]
def ConcreteConvergentRNDEventSpec'.toConcreteConvergentRNDEventSpec [Preorder v] [WellFoundedLT v] [@Machine ACTX AM] [@Machine CTX M] [instR: Refinement AM M]
  (ev : ConcreteConvergentRNDEventSpec' v AM M α) : ConcreteConvergentRNDEventSpec v AM M α Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec
    variant := ev.variant
    simulation := fun m x => by simp ; apply ev.simulation
    convergence := fun m x => by simp ; apply ev.convergence
  }

/-- Variant of `newConcreteConvergentRNDEvent` with implicit `Unit` output type -/
@[simp]
def newConcreteConvergentRNDEvent' [Preorder v] [WellFoundedLT v] [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (ev : ConcreteConvergentRNDEventSpec' v AM M α) : ConvergentRNDEvent v AM M α Unit :=
  newConcreteConvergentRNDEvent ev.toConcreteConvergentRNDEventSpec

/-- Variant of `ConcreteConvergentRNDEventSpec` with implicit `Unit` input and output types -/
structure ConcreteConvergentRNDEventSpec'' (v) [Preorder v] [WellFoundedLT v] (AM) [@Machine ACTX AM] (M) [@Machine CTX M] [instR: Refinement AM M]
  extends _Variant v (M:=M), ConcreteRNDEventSpec'' AM M where

  convergence (m : M):
    Machine.invariant m
    → (grd : guard m)
    → ∀ m', effect m grd m'
            → variant m' < variant m

@[simp]
def ConcreteConvergentRNDEventSpec''.toConcreteConvergentRNDEventSpec [Preorder v] [WellFoundedLT v] [@Machine ACTX AM] [@Machine CTX M] [instR: Refinement AM M]
  (ev : ConcreteConvergentRNDEventSpec'' v AM M) : ConcreteConvergentRNDEventSpec v AM M Unit Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec
    variant := ev.variant
    simulation := fun m grd => by simp ; apply ev.simulation
    convergence := fun m grd => by simp ; apply ev.convergence
  }

/-- Variant of `newConcreteConvergentRNDEvent` with implicit `Unit` input and output types -/
@[simp]
def newConcreteConvergentNDEvent'' [Preorder v] [WellFoundedLT v] [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (ev : ConcreteConvergentRNDEventSpec'' v AM M) : ConvergentRNDEvent v AM M Unit Unit :=
  newConcreteConvergentRNDEvent ev.toConcreteConvergentRNDEventSpec
