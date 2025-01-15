
/-
  Reuse of abstract events (functional refinement)
-/

import LeanMachines.Refinement.Functional.Basic
import LeanMachines.Refinement.Functional.Convergent

import LeanMachines.Refinement.Relational.Abstract

open Refinement
open FRefinement

structure _AbstractFREventSpec (AM) [Machine ACTX AM]
                              (M) [Machine CTX M]
                              [FRefinement AM M] (α) where

  unlift (am am' : AM) (m : M) (x : α): M

@[simp]
def _AbstractFREventSpec.to_AbstractREventSpec [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : _AbstractFREventSpec AM M α) : _AbstractREventSpec AM M α :=
  {
    lift := lift
    lift_ref := lift_ref
    refine_uniq := fun am am' m => by
      intros _ Href₁ Href₂
      simp [refine] at *
      simp [Href₁, Href₂]
    unlift := ev.unlift
  }

structure AbstractFREventSpec (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                             [FRefinement AM M]
  {α β} (abstract : OrdinaryEvent AM α β)
          extends _AbstractFREventSpec AM M α where

  step_ref (m : M) (x : α):
    Machine.invariant m
    → (agrd : abstract.guard (lift m) x)
    → let (_, am') := abstract.action (lift m) x agrd
      refine am' (unlift (lift m) am' m x)

  step_safe (m : M) (x : α):
    Machine.invariant m
    → (agrd : abstract.guard (lift m) x)
    → let (_, am') := abstract.action (lift m) x agrd
      Machine.invariant am' -- redundant but useful
      → Machine.invariant (unlift (lift m) am' m x)

@[simp]
def AbstractFREventSpec.toAbstractREventSpec [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM α β) (ev : AbstractFREventSpec AM M abs) : AbstractREventSpec AM M abs :=
  {
    to_AbstractREventSpec := ev.to_AbstractREventSpec
    step_ref := ev.step_ref
    step_safe := ev.step_safe
  }

@[simp]
def newAbstractFREvent [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM α β) (ev : AbstractFREventSpec AM M abs) : OrdinaryREvent AM M α β :=
  newAbstractREvent abs ev.toAbstractREventSpec

@[simp]
def newAbstractFREvent' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM α Unit) (ev : AbstractFREventSpec AM M abs) : OrdinaryREvent AM M α Unit :=
  newAbstractREvent abs ev.toAbstractREventSpec

structure _AbstractFREventSpec'' (AM) [Machine ACTX AM]
                              (M) [Machine CTX M]
                              [FRefinement AM M] where

  unlift (am am' : AM) (m : M): M

@[simp]
def _AbstractFREventSpec''.to_AbstractFREventSpec [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : _AbstractFREventSpec'' AM M) : _AbstractFREventSpec AM M Unit :=
  {
    unlift := fun am am' m _ => ev.unlift am am' m
  }

structure AbstractFREventSpec'' (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                             [FRefinement AM M]
  (abstract : OrdinaryEvent AM Unit Unit)
          extends _AbstractFREventSpec'' AM M where

  step_ref (m : M):
    Machine.invariant m
    → (agrd : abstract.guard (lift m) ())
    → let (_, am') := abstract.action (lift m) () agrd
      refine am' (unlift (lift m) am' m)

  step_safe (m : M):
    Machine.invariant m
    → (agrd : abstract.guard (lift m) ())
    → let (_, am') := abstract.action (lift m) () agrd
      Machine.invariant am' -- redundant but useful
      → Machine.invariant (unlift (lift m) am' m)

@[simp]
def AbstractFREventSpec''.toAbstractREventSpec [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM Unit Unit) (ev : AbstractFREventSpec'' AM M abs) : AbstractREventSpec AM M abs :=
  {
    to_AbstractREventSpec := ev.to_AbstractFREventSpec''.to_AbstractFREventSpec.to_AbstractREventSpec
    step_ref := fun m () => ev.step_ref m
    step_safe := fun m () => ev.step_safe m
  }

@[simp]
def newAbstractFREvent'' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM Unit Unit) (ev : AbstractFREventSpec'' AM M abs) : OrdinaryREvent AM M Unit Unit :=
  newAbstractREvent abs ev.toAbstractREventSpec

structure AbstractInitFREventSpec (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                             [FRefinement AM M]
  {α β} (abstract : InitEvent AM α β)
          extends _AbstractFREventSpec AM M α where

  step_ref (x : α):
    (agrd : abstract.guard x)
    → let (_, am') := abstract.init x agrd
      refine am' (unlift default am' default x)

  step_safe (x : α):
    (agrd : abstract.guard x)
    → let (_, am') := abstract.init x agrd
      Machine.invariant am' -- redundant but useful
      → Machine.invariant (unlift default am' default x)

@[simp]
def AbstractInitFREventSpec.toAbstractInitREventSpec [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : InitEvent AM α β) (ev : AbstractInitFREventSpec AM M abs) : AbstractInitREventSpec AM M abs :=
  {
    to_AbstractREventSpec := ev.to_AbstractREventSpec
    step_ref := ev.step_ref
    step_safe := ev.step_safe
  }

@[simp]
def newAbstractInitFREvent [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : InitEvent AM α β) (ev : AbstractInitFREventSpec AM M abs) : InitREvent AM M α β :=
  newAbstractInitREvent abs ev.toAbstractInitREventSpec

@[simp]
def newAbstractInitFREvent' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : InitEvent AM α Unit) (ev : AbstractInitFREventSpec AM M abs) : InitREvent AM M α Unit :=
  newAbstractInitREvent abs ev.toAbstractInitREventSpec

structure AbstractInitFREventSpec'' (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                             [FRefinement AM M]
  (abstract : InitEvent AM Unit Unit)
          extends _AbstractFREventSpec'' AM M where

  step_ref:
    (agrd : abstract.guard ())
    → let (_, am') := abstract.init () agrd
      refine am' (unlift default am' default)

  step_safe:
    (agrd : abstract.guard ())
    → let (_, am') := abstract.init () agrd
      Machine.invariant am' -- redundant but useful
      → Machine.invariant (unlift default am' default)

@[simp]
def AbstractInitFREventSpec''.toAbstractInitFREventSpec [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : InitEvent AM Unit Unit) (ev : AbstractInitFREventSpec'' AM M abs) : AbstractInitFREventSpec AM M abs :=
  {
    to_AbstractFREventSpec := ev.to_AbstractFREventSpec
    step_ref := fun () => ev.step_ref
    step_safe := fun () => ev.step_safe
  }

@[simp]
def newAbstractInitFREvent'' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : InitEvent AM Unit Unit) (ev : AbstractInitFREventSpec'' AM M abs) : InitREvent AM M Unit Unit :=
  newAbstractInitFREvent abs ev.toAbstractInitFREventSpec

structure AbstractAnticipatedFREventSpec
              (v) [Preorder v]
              (AM) [Machine ACTX AM]
              (M) [Machine CTX M]
              [FRefinement AM M]
  {α β} (abstract : AnticipatedEvent v AM α β)
          extends AbstractFREventSpec AM M abstract.toOrdinaryEvent where

  step_variant (m : M) (x : α):
    Machine.invariant m
    → (agrd : abstract.guard (lift m) x)
    → let (_, am') := abstract.action (lift m) x agrd
      Machine.invariant am' -- redundant but useful
      → abstract.po.variant (lift (unlift (lift m) am' m x))
      = abstract.po.variant am'

@[simp]
def AbstractAnticipatedFREventSpec.toAbstractAnticipatedREventSpec [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : AnticipatedEvent v AM α β) (ev : AbstractAnticipatedFREventSpec v AM M abs) : AbstractAnticipatedREventSpec v AM M abs :=
  {
    to_AbstractREventSpec := ev.to_AbstractREventSpec
    step_ref := ev.step_ref
    step_safe := ev.step_safe
    step_variant := ev.step_variant
  }

@[simp]
def newAbstractAnticipatedFREvent  [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : AnticipatedEvent v AM α β) (ev : AbstractAnticipatedFREventSpec v AM M abs) : AnticipatedREvent v AM M α β :=
  newAbstractAnticipatedREvent abs ev.toAbstractAnticipatedREventSpec

@[simp]
def newAbstractAnticipatedFREvent'  [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : AnticipatedEvent v AM α Unit) (ev : AbstractAnticipatedFREventSpec v AM M abs) : AnticipatedREvent v AM M α Unit :=
  newAbstractAnticipatedREvent abs ev.toAbstractAnticipatedREventSpec

structure AbstractAnticipatedFREventSpec''
              (v) [Preorder v]
              (AM) [Machine ACTX AM]
              (M) [Machine CTX M]
              [FRefinement AM M]
  (abstract : AnticipatedEvent v AM Unit Unit)
          extends AbstractFREventSpec'' AM M abstract.toOrdinaryEvent where

  step_variant (m : M):
    Machine.invariant m
    → (agrd : abstract.guard (lift m) ())
    → let (_, am') := abstract.action (lift m) () agrd
      Machine.invariant am' -- redundant but useful
      → abstract.po.variant (lift (unlift (lift m) am' m))
      = abstract.po.variant am'

@[simp]
def AbstractAnticipatedFREventSpec''.toAbstractAnticipatedREventSpec [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : AnticipatedEvent v AM Unit Unit) (ev : AbstractAnticipatedFREventSpec'' v AM M abs) : AbstractAnticipatedREventSpec v AM M abs :=
  {
    toAbstractREventSpec := ev.toAbstractFREventSpec''.toAbstractREventSpec
    step_variant := fun m () => ev.step_variant m
  }

@[simp]
def newAbstractAnticipatedFREvent''  [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : AnticipatedEvent v AM Unit Unit) (ev : AbstractAnticipatedFREventSpec'' v AM M abs) : AnticipatedREvent v AM M Unit Unit :=
  newAbstractAnticipatedREvent abs ev.toAbstractAnticipatedREventSpec

@[simp]
def newAbstractConvergentFREvent  [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : ConvergentEvent v AM α β) (ev : AbstractAnticipatedFREventSpec v AM M abs.toAnticipatedEvent) : ConvergentREvent v AM M α β :=
  newAbstractConvergentREvent abs ev.toAbstractAnticipatedREventSpec

@[simp]
def newAbstractConvergentFREvent'  [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : ConvergentEvent v AM α Unit) (ev : AbstractAnticipatedFREventSpec v AM M abs.toAnticipatedEvent) : ConvergentREvent v AM M α Unit :=
  newAbstractConvergentREvent abs ev.toAbstractAnticipatedREventSpec

@[simp]
def newAbstractConvergentFREvent''  [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : ConvergentEvent v AM Unit Unit) (ev : AbstractAnticipatedFREventSpec'' v AM M abs.toAnticipatedEvent) : ConvergentREvent v AM M Unit Unit :=
  newAbstractConvergentREvent abs ev.toAbstractAnticipatedREventSpec
