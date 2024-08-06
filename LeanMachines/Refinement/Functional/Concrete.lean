
import LeanMachines.Refinement.Functional.Basic
import LeanMachines.Refinement.Relational.Concrete

open Refinement
open FRefinement

structure ConcreteFREventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [instFR: FRefinement AM M] (α) (β)
  extends EventSpec M α β where

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let (_, m') := action m x
      lift m = lift (self:=instFR)  m'

@[simp]
def ConcreteFREventSpec.toConcreteREventSpec  [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : ConcreteFREventSpec AM M α β) : ConcreteREventSpec AM M α β :=
  {
    toEventSpec := ev.toEventSpec
    simulation := fun m x => by
      intros Hinv Hgrd am Href
      simp [refine] at *
      have Hsim := ev.simulation m x Hinv Hgrd
      simp at Hsim
      rw [←Hsim]
      assumption
  }

@[simp]
def newConcreteFREvent [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
   (ev : ConcreteFREventSpec AM M α β) : OrdinaryRDetEvent AM M α β :=
  newConcreteREvent ev.toConcreteREventSpec

structure ConcreteFREventSpec' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instFR: FRefinement AM M] (α)
  extends EventSpec' M α where

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := action m x
      lift m = lift (self:=instFR)  m'

@[simp]
def ConcreteFREventSpec'.toConcreteFREventSpec  [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : ConcreteFREventSpec' AM M α) : ConcreteFREventSpec AM M α Unit :=
  {
    toEventSpec := ev.toEventSpec
    simulation := ev.simulation
  }

@[simp]
def newConcreteFREvent' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
   (ev : ConcreteFREventSpec' AM M α) : OrdinaryRDetEvent AM M α Unit :=
  newConcreteREvent ev.toConcreteFREventSpec.toConcreteREventSpec

structure ConcreteFREventSpec'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instFR: FRefinement AM M]
  extends EventSpec'' M where

  simulation (m : M):
    Machine.invariant m
    → guard m
    → let m' := action m
      lift m = lift (self:=instFR)  m'

@[simp]
def ConcreteFREventSpec''.toConcreteFREventSpec [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : ConcreteFREventSpec'' AM M) : ConcreteFREventSpec AM M Unit Unit :=
  {
    toEventSpec := ev.toEventSpec
    simulation := fun m _ => ev.simulation m
  }

@[simp]
def newConcreteFREvent'' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
   (ev : ConcreteFREventSpec'' AM M) : OrdinaryRDetEvent AM M Unit Unit :=
  newConcreteREvent ev.toConcreteFREventSpec.toConcreteREventSpec

/- Anticipated concrete events -/

structure ConcreteAnticipatedFREventSpec (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instFR: FRefinement AM M] (α) (β)
  extends _Variant (M:=M) v, ConcreteFREventSpec AM M α β where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let (_, m') := action m x
      variant m' ≤ variant m

@[simp]
def ConcreteAnticipatedFREventSpec.toConcreteAnticipatedREventSpec  [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : ConcreteAnticipatedFREventSpec v AM M α β) : ConcreteAnticipatedREventSpec v AM M α β :=
  {
    toEventSpec := ev.toEventSpec
    variant := ev.variant
    simulation := ev.toConcreteREventSpec.simulation
    nonIncreasing := ev.nonIncreasing
  }

@[simp]
def newConcreteAnticipatedFREvent [Preorder v] [WellFoundedLT v]
                        [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
   (ev : ConcreteAnticipatedFREventSpec v AM M α β) : AnticipatedRDetEvent v AM M α β :=
  newConcreteAnticipatedREvent ev.toConcreteAnticipatedREventSpec

structure ConcreteAnticipatedFREventSpec' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instFR: FRefinement AM M] (α)
  extends _Variant (M:=M) v, ConcreteREventSpec' AM M α where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := action m x
      variant m' ≤ variant m

@[simp]
def ConcreteAnticipatedFREventSpec'.toConcreteAnticipatedREventSpec  [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : ConcreteAnticipatedFREventSpec' v AM M α) : ConcreteAnticipatedREventSpec v AM M α Unit :=
  {
    toEventSpec := ev.toEventSpec
    variant := ev.variant
    simulation := ev.toConcreteREventSpec'.simulation
    nonIncreasing := ev.nonIncreasing
  }

@[simp]
def newConcreteAnticipatedFREvent' [Preorder v] [WellFoundedLT v]
                        [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
   (ev : ConcreteAnticipatedFREventSpec' v AM M α) : AnticipatedRDetEvent v AM M α Unit :=
  newConcreteAnticipatedREvent ev.toConcreteAnticipatedREventSpec

structure ConcreteAnticipatedFREventSpec'' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instFR: FRefinement AM M]
  extends _Variant (M:=M) v, ConcreteFREventSpec'' AM M where

  nonIncreasing (m : M):
    Machine.invariant m
    → guard m
    → let m' := action m
      variant m' ≤ variant m

@[simp]
def ConcreteAnticipatedFREventSpec''.toConcreteAnticipatedFREventSpec  [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : ConcreteAnticipatedFREventSpec'' v AM M) : ConcreteAnticipatedFREventSpec v AM M Unit Unit :=
  {
    toEventSpec := ev.toEventSpec
    variant := ev.variant
    simulation := fun m _ => ev.simulation m
    nonIncreasing := fun m _ => ev.nonIncreasing m
  }

@[simp]
def newConcreteAnticipatedFREvent'' [Preorder v] [WellFoundedLT v]
                         [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
   (ev : ConcreteAnticipatedFREventSpec'' v AM M) : AnticipatedRDetEvent v AM M Unit Unit :=
  newConcreteAnticipatedREvent ev.toConcreteAnticipatedFREventSpec.toConcreteAnticipatedREventSpec

/- Convergent concrete events -/

structure ConcreteConvergentFREventSpec (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instFR: FRefinement AM M] (α) (β)
  extends _Variant (M:=M) v, ConcreteFREventSpec AM M α β where

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let (_, m') := action m x
      variant m' < variant m

@[simp]
def ConcreteConvergentFREventSpec.toConcreteConvergentREventSpec  [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : ConcreteConvergentFREventSpec v AM M α β) : ConcreteConvergentREventSpec v AM M α β :=
  {
    toEventSpec := ev.toEventSpec
    variant := ev.variant
    simulation := ev.toConcreteREventSpec.simulation
    convergence := ev.convergence
  }

@[simp]
def newConcreteConvergentFREvent [Preorder v] [WellFoundedLT v]
                        [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
   (ev : ConcreteConvergentFREventSpec v AM M α β) : ConvergentRDetEvent v AM M α β :=
  newConcreteConvergentREvent ev.toConcreteConvergentREventSpec

structure ConcreteConvergentFREventSpec' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instFR: FRefinement AM M] (α)
  extends _Variant (M:=M) v, ConcreteREventSpec' AM M α where

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := action m x
      variant m' < variant m

@[simp]
def ConcreteConvergentFREventSpec'.toConcreteConvergentREventSpec  [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : ConcreteConvergentFREventSpec' v AM M α) : ConcreteConvergentREventSpec v AM M α Unit :=
  {
    toEventSpec := ev.toEventSpec
    variant := ev.variant
    simulation := ev.toConcreteREventSpec'.simulation
    convergence := ev.convergence
  }

@[simp]
def newConcreteConvergentFREvent' [Preorder v] [WellFoundedLT v]
                        [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
   (ev : ConcreteConvergentFREventSpec' v AM M α) : ConvergentRDetEvent v AM M α Unit :=
  newConcreteConvergentREvent ev.toConcreteConvergentREventSpec

structure ConcreteConvergentFREventSpec'' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instFR: FRefinement AM M]
  extends _Variant (M:=M) v, ConcreteFREventSpec'' AM M where

  convergence (m : M):
    Machine.invariant m
    → guard m
    → let m' := action m
      variant m' < variant m

@[simp]
def ConcreteConvergentFREventSpec''.toConcreteConvergentFREventSpec  [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : ConcreteConvergentFREventSpec'' v AM M) : ConcreteConvergentFREventSpec v AM M Unit Unit :=
  {
    toEventSpec := ev.toEventSpec
    variant := ev.variant
    simulation := fun m _ => ev.simulation m
    convergence := fun m _ => ev.convergence m
  }

@[simp]
def newConcreteConvergentFREvent'' [Preorder v] [WellFoundedLT v]
                         [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
   (ev : ConcreteConvergentFREventSpec'' v AM M) : ConvergentRDetEvent v AM M Unit Unit :=
  newConcreteConvergentREvent ev.toConcreteConvergentFREventSpec.toConcreteConvergentREventSpec
