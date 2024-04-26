
import EventSystems.Refinement.Functional.Basic
import EventSystems.NonDet.Ordinary
import EventSystems.Refinement.Relational.NonDet.Det.Basic

open Refinement
open FRefinement

structure FRDetEventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M] (α) (β)
  extends EventSpec M α β where

  abstract : OrdinaryNDEvent AM α β

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → abstract.guard (lift m) x

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let (y, m') := action m x
      abstract.effect (lift m) x (y, lift m')

@[simp]
def FRDetEventSpec.toRDetEventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : FRDetEventSpec AM M α β) : RDetEventSpec AM M α β :=
  {
    toEventSpec := ev.toEventSpec

    abstract := ev.abstract

    strengthening := fun m x => by
      intros Hinv Hgrd am Href
      have Hst := ev.strengthening m x Hinv Hgrd
      have Hlr := lift_ref (self:=instFR) m Hinv
      have Huniq := refine_uniq (self:=instFR) am (lift m) m Hinv Href Hlr
      rw [Huniq]
      assumption

    simulation := fun m x => by
      simp
      intros Hinv Hgrd am Href
      have Hlr := lift_ref (self:=instFR) m Hinv
      have Huniq := refine_uniq (self:=instFR) am (lift m) m Hinv Href Hlr
      rw [Huniq]
      have Hsim := ev.simulation m x Hinv Hgrd
      simp at Hsim
      exists (lift (ev.action m x).2)
      constructor
      · assumption
      have Hsafe := ev.safety m x Hinv Hgrd
      exact lift_ref (ev.action m x).2 Hsafe
  }

@[simp]
def newFRDetEvent [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : FRDetEventSpec AM M α β) : OrdinaryRDetEvent AM M α β :=
  newRDetEvent ev.toRDetEventSpec

structure FRDetEventSpec' (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M] (α)
  extends EventSpec' M α where

  abstract : OrdinaryNDEvent AM α Unit

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → abstract.guard (lift m) x

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := action m x
      abstract.effect (lift m) x (y, lift m')

@[simp]
def FRDetEventSpec'.toFRDetEventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : FRDetEventSpec' AM M α) : FRDetEventSpec AM M α Unit :=
  {
    toEventSpec := ev.toEventSpec
    abstract := ev.abstract
    strengthening := ev.strengthening
    simulation := ev.simulation
  }

@[simp]
def newFRDetEvent' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : FRDetEventSpec' AM M α) : OrdinaryRDetEvent AM M α Unit :=
  newRDetEvent ev.toFRDetEventSpec.toRDetEventSpec

structure FRDetEventSpec'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M]
  extends EventSpec'' M where

  abstract : OrdinaryNDEvent AM Unit Unit

  strengthening (m : M):
    Machine.invariant m
    → guard m
    → abstract.guard (lift m) ()

  simulation (m : M):
    Machine.invariant m
    → guard m
    → let m' := action m
      abstract.effect (lift m) () ((), lift m')

@[simp]
def FRDetEventSpec''.toFRDetEventSpec [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : FRDetEventSpec'' AM M) : FRDetEventSpec AM M Unit Unit :=
  {
    toEventSpec := ev.toEventSpec
    abstract := ev.abstract
    strengthening := fun m _ => ev.strengthening m
    simulation := fun m _ => ev.simulation m
  }

@[simp]
def newFRDetEvent'' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : FRDetEventSpec'' AM M) : OrdinaryRDetEvent AM M Unit Unit :=
  newRDetEvent ev.toFRDetEventSpec.toRDetEventSpec

/- Initialization events -/

structure InitFRDetEventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M] (α) (β)
  extends InitEventSpec M α β where

  abstract : InitNDEvent AM α β

  strengthening (x : α):
    guard x
    → abstract.guard Machine.reset x

  simulation (x : α):
    guard x
    → let (y, m') := init x
      abstract.effect Machine.reset x (y, lift m')

@[simp]
def InitFRDetEventSpec.toInitRDetEventSpec  [Machine ACTX AM] [Machine CTX M] [instFR:FRefinement AM M]
  (ev : InitFRDetEventSpec AM M α β) : InitRDetEventSpec AM M α β :=
  {
    toInitEventSpec := ev.toInitEventSpec
    abstract := ev.abstract
    strengthening := ev.strengthening
    simulation := fun x => by
      simp
      intro Hgrd
      have Hsim := ev.simulation x Hgrd
      simp at Hsim
      exists (lift (ev.init x).2)
      simp [Hsim]
      have Hsafe := ev.safety x Hgrd
      apply lift_ref (self:=instFR) (ev.init x).2 Hsafe
  }

@[simp]
def newInitFRDetEvent [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : InitFRDetEventSpec AM M α β) : InitRDetEvent AM M α β :=
  newInitRDetEvent ev.toInitRDetEventSpec

structure InitFRDetEventSpec' (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M] (α)
  extends InitEventSpec' M α where

  abstract : InitNDEvent AM α Unit

  strengthening (x : α):
    guard x
    → abstract.guard Machine.reset x

  simulation (x : α):
    guard x
    → let m' := init x
      abstract.effect Machine.reset x ((), lift m')

@[simp]
def InitFRDetEventSpec'.toInitFRDetEventSpec [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : InitFRDetEventSpec' AM M α) : InitFRDetEventSpec AM M α Unit :=
  {
    toInitEventSpec := ev.toInitEventSpec
    abstract := ev.abstract
    strengthening := ev.strengthening
    simulation := ev.simulation
  }

@[simp]
def newInitFRDetEvent' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : InitFRDetEventSpec' AM M α) : InitRDetEvent AM M α Unit :=
  newInitRDetEvent ev.toInitFRDetEventSpec.toInitRDetEventSpec

structure InitFRDetEventSpec'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M]
  extends InitEventSpec'' M where

  abstract : InitNDEvent AM Unit Unit

  strengthening:
    guard
    → abstract.guard Machine.reset ()

  simulation:
    guard
    → let m' := init
      abstract.effect Machine.reset () ((), lift m')

@[simp]
def InitFRDetEventSpec''.toInitFRDetEventSpec [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : InitFRDetEventSpec'' AM M) : InitFRDetEventSpec AM M Unit Unit :=
  {
    toInitEventSpec := ev.toInitEventSpec
    abstract := ev.abstract
    strengthening := fun _ => ev.strengthening
    simulation := fun _ => ev.simulation
  }

@[simp]
def newInitFRDetEvent'' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : InitFRDetEventSpec'' AM M) : InitRDetEvent AM M Unit Unit :=
  newInitRDetEvent ev.toInitFRDetEventSpec.toInitRDetEventSpec
