
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
                            [FRefinement AM M] (α) (β)
          extends _AbstractFREventSpec AM M α where

  event : OrdinaryEvent AM α β

  step_ref (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → let (_, am') := event.action (lift m) x
      refine am' (unlift (lift m) am' m x)

  step_safe (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → let (_, am') := event.action (lift m) x
      Machine.invariant am' -- redundant but useful
      → Machine.invariant (unlift (lift m) am' m x)

@[simp]
def AbstractFREventSpec.toAbstractREventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : AbstractFREventSpec AM M α β) : AbstractREventSpec AM M α β :=
  {
    to_AbstractREventSpec := ev.to_AbstractREventSpec
    event := ev.event
    step_ref := ev.step_ref
    step_safe := ev.step_safe
  }

@[simp]
def newAbstractFREvent [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : AbstractFREventSpec AM M α β) : OrdinaryREvent AM M α β :=
  newAbstractREvent abs.toAbstractREventSpec

structure AbstractFREventSpec' (AM) [Machine ACTX AM]
                               (M) [Machine CTX M]
                               [FRefinement AM M] (α)
          extends _AbstractFREventSpec AM M α where

  event : OrdinaryEvent AM α Unit

  step_ref (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → let ((), am') := event.action (lift m) x
      refine am' (unlift (lift m) am' m x)

  step_safe (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → let ((), am') := event.action (lift m) x
      Machine.invariant am' -- redundant but useful
      → Machine.invariant (unlift (lift m) am' m x)

@[simp]
def AbstractFREventSpec'.toAbstractREventSpec [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AbstractFREventSpec' AM M α) : AbstractREventSpec AM M α Unit :=
  {
    to_AbstractREventSpec := ev.to_AbstractREventSpec
    event := ev.event
    step_ref := ev.step_ref
    step_safe := ev.step_safe
  }

@[simp]
def newAbstractFREvent' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : AbstractFREventSpec' AM M α) : OrdinaryREvent AM M α Unit :=
  newAbstractREvent abs.toAbstractREventSpec

structure AbstractFREventSpec'' (AM) [Machine ACTX AM]
                               (M) [Machine CTX M]
                               [FRefinement AM M]
          extends _AbstractFREventSpec AM M Unit where

  event : OrdinaryEvent AM Unit Unit

  step_ref (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) ()
    → let ((), am') := event.action (lift m) ()
      refine am' (unlift (lift m) am' m ())

  step_safe (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) ()
    → let ((), am') := event.action (lift m) ()
      Machine.invariant am' -- redundant but useful
      → Machine.invariant (unlift (lift m) am' m ())

@[simp]
def AbstractFREventSpec''.toAbstractREventSpec [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AbstractFREventSpec'' AM M) : AbstractREventSpec AM M Unit Unit :=
  {
    to_AbstractREventSpec := ev.to_AbstractREventSpec
    event := ev.event
    step_ref := ev.step_ref
    step_safe := ev.step_safe
  }

@[simp]
def newAbstractFREvent'' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : AbstractFREventSpec'' AM M) : OrdinaryREvent AM M Unit Unit :=
  newAbstractREvent abs.toAbstractREventSpec

structure AbstractAnticipatedFREventSpec
              (v) [Preorder v]
              (AM) [Machine ACTX AM]
              (M) [Machine CTX M]
              [FRefinement AM M] (α) (β)
          extends _AbstractFREventSpec AM M α where

  event : AnticipatedEvent v AM α β

  step_ref (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → let (_, am') := event.action (lift m) x
      refine am' (unlift (lift m) am' m x)

  step_safe (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → let (_, am') := event.action (lift m) x
      Machine.invariant am' -- redundant but useful
      → Machine.invariant (unlift (lift m) am' m x)

  step_variant (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → let (_, am') := event.action (lift m) x
      Machine.invariant am' -- redundant but useful
      → event.po.variant (lift (unlift (lift m) am' m x))
      = event.po.variant am'

@[simp]
def AbstractAnticipatedFREventSpec.toAbstractAnticipatedREventSpec [Preorder v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : AbstractAnticipatedFREventSpec v AM M α β) : AbstractAnticipatedREventSpec v AM M α β :=
  {
    to_AbstractREventSpec := ev.to_AbstractREventSpec
    event := ev.event
    step_ref := ev.step_ref
    step_safe := ev.step_safe
    step_variant := ev.step_variant
  }

@[simp]
def newAbstractAnticipatedFREvent  [Preorder v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : AbstractAnticipatedFREventSpec v AM M α β) : AnticipatedREvent v AM M α β :=
  newAbstractAnticipatedREvent ev.toAbstractAnticipatedREventSpec

structure AbstractAnticipatedFREventSpec'
              (v) [Preorder v]
              (AM) [Machine ACTX AM]
              (M) [Machine CTX M]
              [FRefinement AM M] (α)
          extends _AbstractFREventSpec AM M α where

  event : AnticipatedEvent v AM α Unit

  step_ref (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → let (_, am') := event.action (lift m) x
      refine am' (unlift (lift m) am' m x)

  step_safe (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → let (_, am') := event.action (lift m) x
      Machine.invariant am' -- redundant but useful
      → Machine.invariant (unlift (lift m) am' m x)

  step_variant (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → let (_, am') := event.action (lift m) x
      Machine.invariant am' -- redundant but useful
      → event.po.variant (lift (unlift (lift m) am' m x))
      = event.po.variant am'

@[simp]
def AbstractAnticipatedFREventSpec'.toAbstractAnticipatedREventSpec [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AbstractAnticipatedFREventSpec' v AM M α) : AbstractAnticipatedREventSpec v AM M α Unit :=
  {
    to_AbstractREventSpec := ev.to_AbstractREventSpec
    event := ev.event
    step_ref := ev.step_ref
    step_safe := ev.step_safe
    step_variant := ev.step_variant
  }

@[simp]
def newAbstractAnticipatedFREvent'  [Preorder v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : AbstractAnticipatedFREventSpec' v AM M α) : AnticipatedREvent v AM M α Unit :=
  newAbstractAnticipatedREvent ev.toAbstractAnticipatedREventSpec

structure AbstractAnticipatedFREventSpec''
              (v) [Preorder v]
              (AM) [Machine ACTX AM]
              (M) [Machine CTX M]
              [FRefinement AM M]
          extends _AbstractFREventSpec AM M Unit where

  event : AnticipatedEvent v AM Unit Unit

  step_ref (m : M):
    Machine.invariant m
    → event.guard (lift m) ()
    → let (_, am') := event.action (lift m) ()
      refine am' (unlift (lift m) am' m ())

  step_safe (m : M):
    Machine.invariant m
    → event.guard (lift m) ()
    → let (_, am') := event.action (lift m) ()
      Machine.invariant am' -- redundant but useful
      → Machine.invariant (unlift (lift m) am' m ())

  step_variant (m : M):
    Machine.invariant m
    → event.guard (lift m) ()
    → let (_, am') := event.action (lift m) ()
      Machine.invariant am' -- redundant but useful
      → event.po.variant (lift (unlift (lift m) am' m ()))
      = event.po.variant am'

@[simp]
def AbstractAnticipatedFREventSpec''.toAbstractAnticipatedREventSpec [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AbstractAnticipatedFREventSpec'' v AM M) : AbstractAnticipatedREventSpec v AM M Unit Unit :=
  {
    to_AbstractREventSpec := ev.to_AbstractREventSpec
    event := ev.event
    step_ref := fun m _ => ev.step_ref m
    step_safe := fun m _ => ev.step_safe m
    step_variant := fun m _ => ev.step_variant m
  }

@[simp]
def newAbstractAnticipatedFREvent''  [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AbstractAnticipatedFREventSpec'' v AM M) : AnticipatedREvent v AM M Unit Unit :=
  newAbstractAnticipatedREvent ev.toAbstractAnticipatedREventSpec


structure AbstractConvergentFREventSpec
              (v) [Preorder v] [WellFoundedLT v]
              (AM) [Machine ACTX AM]
              (M) [Machine CTX M]
              [FRefinement AM M] (α) (β)
          extends _AbstractFREventSpec AM M α where

  event : ConvergentEvent v AM α β

  step_ref (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → let (_, am') := event.action (lift m) x
      refine am' (unlift (lift m) am' m x)

  step_safe (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → let (_, am') := event.action (lift m) x
      Machine.invariant am' -- redundant but useful
      → Machine.invariant (unlift (lift m) am' m x)

  step_variant (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → let (_, am') := event.action (lift m) x
      Machine.invariant am' -- redundant but useful
      → event.po.variant (lift (unlift (lift m) am' m x))
      = event.po.variant am'

@[simp]
def AbstractConvergentFREventSpec.toAbstractConvergentREventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AbstractConvergentFREventSpec v AM M α β) : AbstractConvergentREventSpec v AM M α β :=
  {
    to_AbstractREventSpec := ev.to_AbstractREventSpec
    event := ev.event
    step_ref := ev.step_ref
    step_safe := ev.step_safe
    step_variant := ev.step_variant
  }

@[simp]
def newAbstractConvergentFREvent  [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : AbstractConvergentFREventSpec v AM M α β) : ConvergentREvent v AM M α β :=
  newAbstractConvergentREvent ev.toAbstractConvergentREventSpec

structure AbstractConvergentFREventSpec'
              (v) [Preorder v] [WellFoundedLT v]
              (AM) [Machine ACTX AM]
              (M) [Machine CTX M]
              [FRefinement AM M] (α)
          extends _AbstractFREventSpec AM M α where

  event : ConvergentEvent v AM α Unit

  step_ref (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → let (_, am') := event.action (lift m) x
      refine am' (unlift (lift m) am' m x)

  step_safe (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → let (_, am') := event.action (lift m) x
      Machine.invariant am' -- redundant but useful
      → Machine.invariant (unlift (lift m) am' m x)

  step_variant (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → let (_, am') := event.action (lift m) x
      Machine.invariant am' -- redundant but useful
      → event.po.variant (lift (unlift (lift m) am' m x))
      = event.po.variant am'

@[simp]
def AbstractConvergentFREventSpec'.toAbstractConvergentREventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AbstractConvergentFREventSpec' v AM M α) : AbstractConvergentREventSpec v AM M α Unit :=
  {
    to_AbstractREventSpec := ev.to_AbstractREventSpec
    event := ev.event
    step_ref := ev.step_ref
    step_safe := ev.step_safe
    step_variant := ev.step_variant
  }

@[simp]
def newAbstractConvergentFREvent'  [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : AbstractConvergentFREventSpec' v AM M α) : ConvergentREvent v AM M α Unit :=
  newAbstractConvergentREvent ev.toAbstractConvergentREventSpec

structure AbstractConvergentFREventSpec''
              (v) [Preorder v] [WellFoundedLT v]
              (AM) [Machine ACTX AM]
              (M) [Machine CTX M]
              [FRefinement AM M]
          extends _AbstractFREventSpec AM M Unit where

  event : ConvergentEvent v AM Unit Unit

  step_ref (m : M):
    Machine.invariant m
    → event.guard (lift m) ()
    → let (_, am') := event.action (lift m) ()
      refine am' (unlift (lift m) am' m ())

  step_safe (m : M):
    Machine.invariant m
    → event.guard (lift m) ()
    → let (_, am') := event.action (lift m) ()
      Machine.invariant am' -- redundant but useful
      → Machine.invariant (unlift (lift m) am' m ())

  step_variant (m : M):
    Machine.invariant m
    → event.guard (lift m) ()
    → let (_, am') := event.action (lift m) ()
      Machine.invariant am' -- redundant but useful
      → event.po.variant (lift (unlift (lift m) am' m ()))
      = event.po.variant am'

@[simp]
def AbstractConvergentFREventSpec''.toAbstractConvergentREventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AbstractConvergentFREventSpec'' v AM M) : AbstractConvergentREventSpec v AM M Unit Unit :=
  {
    to_AbstractREventSpec := ev.to_AbstractREventSpec
    event := ev.event
    step_ref := fun m _ => ev.step_ref m
    step_safe := fun m _ => ev.step_safe m
    step_variant := fun m _ => ev.step_variant m
  }

@[simp]
def newAbstractConvergentFREvent''  [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AbstractConvergentFREventSpec'' v AM M) : ConvergentREvent v AM M Unit Unit :=
  newAbstractConvergentREvent ev.toAbstractConvergentREventSpec
