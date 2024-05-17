
/-
  Reuse of abstract events (functional refinement)
-/

import EventSystems.Refinement.Functional.Basic
import EventSystems.Refinement.Functional.Convergent

import EventSystems.Refinement.Relational.Abstract

open Refinement
open FRefinement

structure _AbstractFREventSpec (AM) [Machine ACTX AM]
                              (M) [Machine CTX M]
                              [FRefinement AM M] (α) where

  unlift (am am' : AM) (m : M) (x : α): M

@[simp]
def _AbstractFREventSpec.to_AbstractREventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : _AbstractFREventSpec AM M α) : _AbstractREventSpec AM M α :=
  {
    lift := lift
    lift_ref := lift_ref
    refine_uniq := refine_uniq
    unlift := ev.unlift
  }

structure AbstractFREventSpec (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                             [FRefinement AM M]
  {α β} (abstract : _Event AM α β)
          extends _AbstractFREventSpec AM M α where

  step_ref (m : M) (x : α):
    Machine.invariant m
    → abstract.guard (lift m) x
    → let (_, am') := abstract.action (lift m) x
      refine am' (unlift (lift m) am' m x)

  step_safe (m : M) (x : α):
    Machine.invariant m
    → abstract.guard (lift m) x
    → let (_, am') := abstract.action (lift m) x
      Machine.invariant am' -- redundant but useful
      → Machine.invariant (unlift (lift m) am' m x)

@[simp]
def AbstractFREventSpec.toAbstractREventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (abs : _Event AM α β) (ev : AbstractFREventSpec AM M abs) : AbstractREventSpec AM M abs :=
  {
    to_AbstractREventSpec := ev.to_AbstractREventSpec
    step_ref := ev.step_ref
    step_safe := ev.step_safe
  }

@[simp]
def newAbstractFREvent [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM α β) (ev : AbstractFREventSpec AM M abs.to_Event) : OrdinaryREvent AM M α β :=
  newAbstractREvent abs ev.toAbstractREventSpec

@[simp]
def newAbstractFREvent' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM α Unit) (ev : AbstractFREventSpec AM M abs.to_Event) : OrdinaryREvent AM M α Unit :=
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
  (abstract : _Event AM Unit Unit)
          extends _AbstractFREventSpec'' AM M where

  step_ref (m : M):
    Machine.invariant m
    → abstract.guard (lift m) ()
    → let (_, am') := abstract.action (lift m) ()
      refine am' (unlift (lift m) am' m)

  step_safe (m : M):
    Machine.invariant m
    → abstract.guard (lift m) ()
    → let (_, am') := abstract.action (lift m) ()
      Machine.invariant am' -- redundant but useful
      → Machine.invariant (unlift (lift m) am' m)

@[simp]
def AbstractFREventSpec''.toAbstractREventSpec [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : _Event AM Unit Unit) (ev : AbstractFREventSpec'' AM M abs) : AbstractREventSpec AM M abs :=
  {
    to_AbstractREventSpec := ev.to_AbstractFREventSpec''.to_AbstractFREventSpec.to_AbstractREventSpec
    step_ref := fun m () => ev.step_ref m
    step_safe := fun m () => ev.step_safe m
  }

@[simp]
def newAbstractFREvent'' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM Unit Unit) (ev : AbstractFREventSpec'' AM M abs.to_Event) : OrdinaryREvent AM M Unit Unit :=
  newAbstractREvent abs ev.toAbstractREventSpec

structure AbstractInitFREventSpec (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                             [FRefinement AM M]
  {α β} (abstract : _Event AM α β)
          extends _AbstractFREventSpec AM M α where

  step_ref (x : α):
    abstract.guard Machine.reset x
    → let (_, am') := abstract.action Machine.reset x
      refine am' (unlift Machine.reset am' Machine.reset x)

  step_safe (x : α):
    abstract.guard Machine.reset x
    → let (_, am') := abstract.action Machine.reset x
      Machine.invariant am' -- redundant but useful
      → Machine.invariant (unlift Machine.reset am' Machine.reset x)

@[simp]
def AbstractInitFREventSpec.toAbstractInitREventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (abs : _Event AM α β) (ev : AbstractInitFREventSpec AM M abs) : AbstractInitREventSpec AM M abs :=
  {
    to_AbstractREventSpec := ev.to_AbstractREventSpec
    step_ref := ev.step_ref
    step_safe := ev.step_safe
  }

@[simp]
def newAbstractInitFREvent [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : InitEvent AM α β) (ev : AbstractInitFREventSpec AM M abs.to_Event) : InitREvent AM M α β :=
  newAbstractInitREvent abs ev.toAbstractInitREventSpec

@[simp]
def newAbstractInitFREvent' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : InitEvent AM α Unit) (ev : AbstractInitFREventSpec AM M abs.to_Event) : InitREvent AM M α Unit :=
  newAbstractInitREvent abs ev.toAbstractInitREventSpec

structure AbstractInitFREventSpec'' (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                             [FRefinement AM M]
  (abstract : _Event AM Unit Unit)
          extends _AbstractFREventSpec'' AM M where

  step_ref:
    abstract.guard Machine.reset ()
    → let (_, am') := abstract.action Machine.reset ()
      refine am' (unlift Machine.reset am' Machine.reset)

  step_safe:
    abstract.guard Machine.reset ()
    → let (_, am') := abstract.action Machine.reset ()
      Machine.invariant am' -- redundant but useful
      → Machine.invariant (unlift Machine.reset am' Machine.reset)

@[simp]
def AbstractInitFREventSpec''.toAbstractInitFREventSpec [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : _Event AM Unit Unit) (ev : AbstractInitFREventSpec'' AM M abs) : AbstractInitFREventSpec AM M abs :=
  {
    to_AbstractFREventSpec := ev.to_AbstractFREventSpec
    step_ref := fun () => ev.step_ref
    step_safe := fun () => ev.step_safe
  }

@[simp]
def newAbstractInitFREvent'' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : InitEvent AM Unit Unit) (ev : AbstractInitFREventSpec'' AM M abs.to_Event) : InitREvent AM M Unit Unit :=
  newAbstractInitFREvent abs ev.toAbstractInitFREventSpec

structure AbstractAnticipatedFREventSpec
              (v) [Preorder v]
              (AM) [Machine ACTX AM]
              (M) [Machine CTX M]
              [FRefinement AM M]
  {α β} (abstract : AnticipatedEvent v AM α β)
          extends AbstractFREventSpec AM M abstract.to_Event where

  step_variant (m : M) (x : α):
    Machine.invariant m
    → abstract.guard (lift m) x
    → let (_, am') := abstract.action (lift m) x
      Machine.invariant am' -- redundant but useful
      → abstract.po.variant (lift (unlift (lift m) am' m x))
      = abstract.po.variant am'

@[simp]
def AbstractAnticipatedFREventSpec.toAbstractAnticipatedREventSpec [Preorder v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (abs : AnticipatedEvent v AM α β) (ev : AbstractAnticipatedFREventSpec v AM M abs) : AbstractAnticipatedREventSpec v AM M abs :=
  {
    to_AbstractREventSpec := ev.to_AbstractREventSpec
    step_ref := ev.step_ref
    step_safe := ev.step_safe
    step_variant := ev.step_variant
  }

@[simp]
def newAbstractAnticipatedFREvent  [Preorder v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (abs : AnticipatedEvent v AM α β) (ev : AbstractAnticipatedFREventSpec v AM M abs) : AnticipatedREvent v AM M α β :=
  newAbstractAnticipatedREvent abs ev.toAbstractAnticipatedREventSpec

@[simp]
def newAbstractAnticipatedFREvent'  [Preorder v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (abs : AnticipatedEvent v AM α Unit) (ev : AbstractAnticipatedFREventSpec v AM M abs) : AnticipatedREvent v AM M α Unit :=
  newAbstractAnticipatedREvent abs ev.toAbstractAnticipatedREventSpec

structure AbstractAnticipatedFREventSpec''
              (v) [Preorder v]
              (AM) [Machine ACTX AM]
              (M) [Machine CTX M]
              [FRefinement AM M]
  (abstract : AnticipatedEvent v AM Unit Unit)
          extends AbstractFREventSpec'' AM M abstract.to_Event where

  step_variant (m : M):
    Machine.invariant m
    → abstract.guard (lift m) ()
    → let (_, am') := abstract.action (lift m) ()
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
def newAbstractConvergentFREvent  [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (abs : ConvergentEvent v AM α β) (ev : AbstractAnticipatedFREventSpec v AM M abs.toAnticipatedEvent) : ConvergentREvent v AM M α β :=
  newAbstractConvergentREvent abs ev.toAbstractAnticipatedREventSpec

@[simp]
def newAbstractConvergentFREvent'  [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (abs : ConvergentEvent v AM α Unit) (ev : AbstractAnticipatedFREventSpec v AM M abs.toAnticipatedEvent) : ConvergentREvent v AM M α Unit :=
  newAbstractConvergentREvent abs ev.toAbstractAnticipatedREventSpec

@[simp]
def newAbstractConvergentFREvent''  [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : ConvergentEvent v AM Unit Unit) (ev : AbstractAnticipatedFREventSpec'' v AM M abs.toAnticipatedEvent) : ConvergentREvent v AM M Unit Unit :=
  newAbstractConvergentREvent abs ev.toAbstractAnticipatedREventSpec
