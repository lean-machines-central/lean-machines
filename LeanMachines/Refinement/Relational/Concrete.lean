import LeanMachines.Event.Ordinary
import LeanMachines.Event.Convergent
import LeanMachines.NonDet.Basic
import LeanMachines.Refinement.Relational.Basic
import LeanMachines.Refinement.Relational.NonDet.Det.Convergent

/-!

# Defining new, concrete events

Concrete events are events only available at the concrete level
when defining a refined machine.

Concrete events refine the (non-deterministic) `skip` event.

(the discussion below can be safely skipped)

If compared to the Event-B notion of a concrete event, there
is an important difference since we do not enforce the anticipation
or convergence of concrete events.  Of course, anticipation or
convergence or concrete event is a possible requirement, only
not mandatory.

The argument in favor of convergence is that the abstract skip
event cannot be infinitely triggered if the concrete event is
convergence (which, thanks to anticipation, can be postponed to
a further refinement).  The main counter-argument, which is the
reason why this is not enforced in LeanMachines, is that a concrete
event may not be able to define an interesting, and varying variant.
In our opinion, this is more related to a *fairness* argument
(at the abstract level), which may or may not be a desirable
requirement.

-/

open Refinement

/-!
## Concrete ordinary events
-/

/-- The specification of a concrete (ordinary) event, refining (non-deterministic) Skip.-/
structure ConcreteREventSpec (AM) [instAM: Machine ACTX AM]
                             (M) [instM: Machine CTX M]
                            [instR: Refinement AM M] (α) (β)
          extends EventSpec M α β where

  /-- Proof obligation: the refined event safely simulates the non-deterministic Skip event
   (no state change at the abstract level). -/
  simulation (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ am, refine (self:=instR) am m
      →  refine (self:=instR) am (action m x grd).2

/-- The construction of a concrete (ordinary) event from a `ConcreteREventSpec` specification. -/
@[simp]
def newConcreteREvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   (ev : ConcreteREventSpec AM M α β) : OrdinaryRDetEvent AM M α β :=
  {
    to_Event := ev.to_Event
    po := {
      lift_in := id
      lift_out := id
      safety := ev.safety
      abstract := skip_NDEvent
      strengthening := fun m x => by simp
      simulation := fun m x => by simp ; apply ev.simulation
    }
  }

/-
  XXX : there is some redundancy below because of a strange unification issue ...
-/

/-- Variant of `ConcreteREventSpec` with implicit `Unit` output type -/
structure ConcreteREventSpec' (AM) [instAM: Machine ACTX AM]
                             (M) [instM: Machine CTX M]
                            [instR: Refinement AM M] (α)
          extends EventSpec' M α where

  simulation (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ am, refine (self:=instR) am m
      →  refine (self:=instR) am (action m x grd)

/-- Variant of `newConcreteREvent` with implicit `Unit` output type -/
@[simp]
def newConcreteREvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   (ev : ConcreteREventSpec' AM M α) : OrdinaryRDetEvent AM M α Unit :=
  {
    to_Event := ev.toEventSpec.to_Event
    po := {
      lift_in := id
      lift_out := id
      safety := ev.safety
      abstract := skip_NDEvent
      strengthening := fun m x => by simp
      simulation := fun m x => by simp ; apply ev.simulation
    }
  }

/-- Variant of `ConcreteREventSpec` with implicit `Unit` input and output types -/
structure ConcreteREventSpec'' (AM) [instAM: Machine ACTX AM]
                             (M) [instM: Machine CTX M]
                             [instR: Refinement AM M]
          extends EventSpec'' M where

  simulation (m : M):
    Machine.invariant m
    → (grd : guard m)
    → ∀ am, refine (self:=instR) am m
      →  refine (self:=instR) am (action m grd)

/-- Variant of `newConcreteREvent` with implicit `Unit` input and output types -/
@[simp]
def newConcreteREvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   (ev : ConcreteREventSpec'' AM M) : OrdinaryRDetEvent AM M Unit Unit :=
  {
    to_Event := ev.toEventSpec.to_Event
    po := {
      lift_in := id
      lift_out := id
      safety := fun m _ => ev.safety m
      abstract := skip_NDEvent
      strengthening := fun m _ => by simp
      simulation := fun m x => by simp ; apply ev.simulation
    }
  }

/-
structure ConcreteInitREventSpec (AM) [instAM: Machine ACTX AM]
                                 (M) [instM: Machine CTX M]
                                 [instR: Refinement AM M] (α) (β) [Inhabited β]
     where

  guard (x : α) : Prop
  init (x : α) : β × M

  safety (x : α) :
    guard x
    → Machine.invariant (init x).snd

  simulation (x : α):
    guard x
    → refine (self:=instR) Machine.reset (init x).2

-- **Remark** : ConcreteInit is not possible because
-- the destination state of  Skip from Machine.reset
-- is Machine.reset, which is not a proper destination
-- state (in particular, there is no invariant enforced)

-/

/-!
## Concrete anticipated events

**Remark**:  for Event-B (conceptual) compatibility, this is the minimal set of requirements
for introducing new, concrete events in a refined machine.
-/

/-- The specification of a concrete anticipated event, with the requirements
of `ConcreteREventSpec` together with anticipation requirements (variant, etc).-/
structure ConcreteAnticipatedREventSpec (v) [Preorder v] [WellFoundedLT v]
                             (AM) [instAM: Machine ACTX AM]
                             (M) [instM: Machine CTX M]
                            [instR: Refinement AM M] (α) (β)
          extends _Variant (M:=M) v, ConcreteREventSpec AM M α β where

  /-- Proof obligation: the concrete variant does not increases. -/
  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → let m' := (action m x grd).2
      variant m' ≤ variant m

/-- The construction of a concrete anticipated event from a `ConcreteAnticipatedREventSpec` specification. -/
@[simp]
def newConcreteAnticipatedREvent [Preorder v] [WellFoundedLT v]
                       [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   (ev : ConcreteAnticipatedREventSpec v AM M α β) : AnticipatedRDetEvent v AM M α β :=
  {
    to_Event := ev.to_Event
    po := {
      lift_in := id
      lift_out := id
      safety := ev.safety
      abstract := skip_NDEvent
      strengthening := fun m x => by simp
      simulation := fun m x => by simp ; apply ev.simulation
      variant := ev.variant
      nonIncreasing := fun m x => by
        simp
        intros Hinv Hgrd
        exact ev.nonIncreasing m x Hinv Hgrd
    }
  }

/-- Variant of `ConcreteAnticipatedREventSpec` with implicit `Unit` output type -/
structure ConcreteAnticipatedREventSpec' (v) [Preorder v] [WellFoundedLT v]
                             (AM) [instAM: Machine ACTX AM]
                             (M) [instM: Machine CTX M]
                            [instR: Refinement AM M] (α)
          extends _Variant (M:=M) v, ConcreteREventSpec' AM M α where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → let m' := (action m x grd)
      variant m' ≤ variant m

/-- Variant of `newConcreteAnticipatedREvent` with implicit `Unit` output type -/
@[simp]
def newConcreteAnticipatedREvent' [Preorder v] [WellFoundedLT v]
                       [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   (ev : ConcreteAnticipatedREventSpec' v AM M α) : AnticipatedRDetEvent v AM M α Unit :=
  {
    to_Event := ev.toEventSpec.to_Event
    po := {
      lift_in := id
      lift_out := id
      safety := ev.safety
      abstract := skip_NDEvent
      strengthening := fun m x => by simp
      simulation := fun m x => by simp ; apply ev.simulation
      variant := ev.variant
      nonIncreasing := fun m x => by
        simp
        intros Hinv Hgrd
        exact ev.nonIncreasing m x Hinv Hgrd
    }
  }

/-- Variant of `ConcreteAnticipatedREventSpec` with implicit `Unit` input and output types -/
structure ConcreteAnticipatedREventSpec'' (v) [Preorder v] [WellFoundedLT v]
                             (AM) [instAM: Machine ACTX AM]
                             (M) [instM: Machine CTX M]
                             [instR: Refinement AM M]
          extends _Variant (M:=M) v, ConcreteREventSpec'' AM M where

  nonIncreasing (m : M):
    Machine.invariant m
    → (grd : guard m)
    → let m' := action m grd
      variant m' ≤ variant m

/-- Variant of `newConcreteAnticipatedREvent` with implicit `Unit` input and output types -/
@[simp]
def newConcreteAnticipatedREvent'' [Preorder v] [WellFoundedLT v]
                       [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   (ev : ConcreteAnticipatedREventSpec'' v AM M) : AnticipatedRDetEvent v AM M Unit Unit :=
  {
    to_Event := ev.toEventSpec.to_Event
    po := {
      lift_in := id
      lift_out := id
      safety := fun m _ => ev.safety m
      abstract := skip_NDEvent
      strengthening := fun m _ => by simp
      simulation := fun m x => by simp ; apply ev.simulation
      variant := ev.variant
      nonIncreasing := fun m x => by
        simp
        intros Hinv Hgrd
        exact ev.nonIncreasing m Hinv Hgrd
    }
  }

/-!
## Concrete convergent events
-/

/-- The specification of a concrete convergent event, with the requirements
of `ConcreteREventSpec` together with convergence requirements (variant, etc).-/
structure ConcreteConvergentREventSpec (v) [Preorder v] [WellFoundedLT v]
                             (AM) [instAM: Machine ACTX AM]
                             (M) [instM: Machine CTX M]
                            [instR: Refinement AM M] (α) (β)
          extends _Variant (M:=M) v, ConcreteREventSpec AM M α β where

  /-- Proof obligation: the variant strictly decrases. -/
  convergence (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → let m' := (action m x grd).2
      variant m' < variant m

/-- The construction of a concrete convergent event from a `ConcreteConvergentREventSpec` specification. -/
@[simp]
def newConcreteConvergentREvent [Preorder v] [WellFoundedLT v]
                       [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   (ev : ConcreteConvergentREventSpec v AM M α β) : ConvergentRDetEvent v AM M α β :=
  {
    to_Event := ev.to_Event
    po := {
      lift_in := id
      lift_out := id
      safety := ev.safety
      abstract := skip_NDEvent
      strengthening := fun m x => by simp
      simulation := fun m x => by simp ; apply ev.simulation
      variant := ev.variant
      nonIncreasing := fun m x => by
        simp
        intros Hinv Hgrd
        have Hcv := ev.convergence m x Hinv Hgrd
        simp at Hcv
        exact le_of_lt Hcv
      convergence := ev.convergence
    }
  }

/-- Variant of `ConcreteConvergentREventSpec` with implicit `Unit` output type -/
structure ConcreteConvergentREventSpec' (v) [Preorder v] [WellFoundedLT v]
                             (AM) [instAM: Machine ACTX AM]
                             (M) [instM: Machine CTX M]
                            [instR: Refinement AM M] (α)
          extends _Variant (M:=M) v, ConcreteREventSpec' AM M α where

  convergence (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → let m' := (action m x grd)
      variant m' < variant m

/-- Variant of `newConcreteConvergentREvent` with implicit `Unit` output type -/
@[simp]
def newConcreteConvergentREvent' [Preorder v] [WellFoundedLT v]
                       [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   (ev : ConcreteConvergentREventSpec' v AM M α) : ConvergentRDetEvent v AM M α Unit :=
  {
    to_Event := ev.toEventSpec.to_Event
    po := {
      lift_in := id
      lift_out := id
      safety := ev.safety
      abstract := skip_NDEvent
      strengthening := fun m x => by simp
      simulation := fun m x => by simp ; apply ev.simulation
      variant := ev.variant
      nonIncreasing := fun m x => by simp
                                     intros Hinv Hgrd
                                     have Hcv := ev.convergence m x Hinv Hgrd
                                     simp at Hcv
                                     exact le_of_lt Hcv
      convergence := ev.convergence
    }
  }

/-- Variant of `ConcreteConvergentREventSpec` with implicit `Unit` input and output types -/
structure ConcreteConvergentREventSpec'' (v) [Preorder v] [WellFoundedLT v]
                             (AM) [instAM: Machine ACTX AM]
                             (M) [instM: Machine CTX M]
                             [instR: Refinement AM M]
          extends _Variant (M:=M) v, ConcreteREventSpec'' AM M where

  convergence (m : M):
    Machine.invariant m
    → (grd : guard m)
    → let m' := action m grd
      variant m' < variant m

/-- Variant of `newConcreteConvergentREvent` with implicit `Unit` input and output types -/
@[simp]
def newConcreteConvergentREvent'' [Preorder v] [WellFoundedLT v]
                       [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   (ev : ConcreteConvergentREventSpec'' v AM M) : ConvergentRDetEvent v AM M Unit Unit :=
  {
    to_Event := ev.toEventSpec.to_Event
    po := {
      lift_in := id
      lift_out := id
      safety := fun m _ => ev.safety m
      abstract := skip_NDEvent
      strengthening := fun m _ => by simp
      simulation := fun m x => by simp ; apply ev.simulation
      variant := ev.variant
      nonIncreasing := fun m x => by simp
                                     intros Hinv Hgrd
                                     have Hcv := ev.convergence m Hinv Hgrd
                                     simp at Hcv
                                     exact le_of_lt Hcv
      convergence := fun m _ => ev.convergence m
    }
  }
