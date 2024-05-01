
import EventSystems.NonDet.Basic
import EventSystems.NonDet.Ordinary
import EventSystems.Refinement.Relational.NonDet.Basic
import EventSystems.Refinement.Functional.Basic

open Refinement
open FRefinement

structure FRNDEventSpec (AM) [Machine ACTX AM]
                        (M) [Machine CTX M]
                        [FRefinement AM M] (α) (β)
  extends NDEventSpec M α β where

  abstract : OrdinaryNDEvent AM α β

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → abstract.guard (lift m) x

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ y, ∀ m', effect m x (y, m')
      → abstract.effect (lift m) x (y, (lift m'))

@[simp]
def FRNDEventSpec.toRNDEventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : FRNDEventSpec AM M α β) : RNDEventSpec AM M α β :=
  {
    toNDEventSpec := ev.toNDEventSpec
    abstract := ev.abstract
    strengthening := fun m x => lift_strengthening m x ev.abstract.guard ev.guard (ev.strengthening m x)
    simulation := fun m x => by intros Hinv Hgrd y m' Heff am Href
                                have Hsim := ev.simulation m x Hinv Hgrd y m' Heff
                                exists (lift m')
                                have Href' := lift_ref (self:=instFR) m Hinv
                                have Huniq := refine_uniq (self:=instFR) am (lift m) m Hinv Href Href'
                                rw [Huniq]
                                simp [Hsim]
                                have Hinv' := ev.safety m x Hinv Hgrd y m' Heff
                                exact lift_ref m' Hinv'
  }

@[simp]
def newFRNDEvent [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : FRNDEventSpec AM M α β) : OrdinaryRNDEvent AM M α β :=
  newRNDEvent ev.toRNDEventSpec

structure FRNDEventSpec' (AM) [Machine ACTX AM]
                         (M) [Machine CTX M]
                         [FRefinement AM M] (α)
  extends NDEventSpec' M α where

  abstract : OrdinaryNDEvent AM α Unit

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → abstract.guard (lift m) x

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ m', effect m x m'
      → abstract.effect (lift m) x ((), (lift m'))

@[simp]
def FRNDEventSpec'.toFRNDEventSpec [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : FRNDEventSpec' AM M α) : FRNDEventSpec AM M α Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec
    abstract := ev.abstract
    strengthening := ev.strengthening
    simulation := fun m x => by simp
                                intros Hinv Hgrd _ m' Heff
                                apply ev.simulation <;> assumption
  }

@[simp]
def newFRNDEvent' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : FRNDEventSpec' AM M α) : OrdinaryRNDEvent AM M α Unit :=
  newFRNDEvent ev.toFRNDEventSpec

structure FRNDEventSpec'' (AM) [Machine ACTX AM]
                         (M) [Machine CTX M]
                         [FRefinement AM M]
  extends NDEventSpec'' M where

  abstract : OrdinaryNDEvent AM Unit Unit

  strengthening (m : M):
    Machine.invariant m
    → guard m
    → abstract.guard (lift m) ()

  simulation (m : M):
    Machine.invariant m
    → guard m
    → ∀ m', effect m m'
      → abstract.effect (lift m) () ((), (lift m'))

@[simp]
def FRNDEventSpec''.toFRNDEventSpec [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : FRNDEventSpec'' AM M) : FRNDEventSpec AM M Unit Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec
    abstract := ev.abstract
    strengthening := fun m _ => ev.strengthening m
    simulation := fun m x => by simp
                                intros Hinv Hgrd _ m' Heff
                                apply ev.simulation <;> assumption
  }

@[simp]
def newFRNDEvent'' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : FRNDEventSpec'' AM M) : OrdinaryRNDEvent AM M Unit Unit :=
  newFRNDEvent ev.toFRNDEventSpec

/- Initialization events -/

structure InitFRNDEventSpec (AM) [Machine ACTX AM]
                        (M) [Machine CTX M]
                        [FRefinement AM M] (α) (β)
  extends InitNDEventSpec M α β where

  abstract : InitNDEvent AM α β

  strengthening (x : α):
    guard x
    → abstract.guard Machine.reset x

  simulation (x : α):
    guard x
    → ∀ y, ∀ m', init x (y, m')
      → abstract.effect Machine.reset x (y, (lift m'))

@[simp]
def InitFRNDEventSpec.toInitRNDEventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : InitFRNDEventSpec AM M α β) : InitRNDEventSpec AM M α β :=
  {
    toInitNDEventSpec := ev.toInitNDEventSpec
    abstract := ev.abstract
    strengthening := ev.strengthening
    simulation := fun m x => by
      intros y m' Hinit
      have Hsim := ev.simulation m x y m' Hinit
      exists (lift m')
      simp [Hsim]
      -- automatic from here
      refine lift_ref m' ?_
      exact ev.safety m x y m' Hinit
  }

@[simp]
def newInitFRNDEvent [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : InitFRNDEventSpec AM M α β) : InitRNDEvent AM M α β :=
  newInitRNDEvent ev.toInitRNDEventSpec

structure InitFRNDEventSpec' (AM) [Machine ACTX AM]
                        (M) [Machine CTX M]
                        [FRefinement AM M] (α)
  extends InitNDEventSpec' M α where

  abstract : InitNDEvent AM α Unit

  strengthening (x : α):
    guard x
    → abstract.guard Machine.reset x

  simulation (x : α):
    guard x
    → ∀ m', init x m'
      → abstract.effect Machine.reset x ((), (lift m'))

@[simp]
def InitFRNDEventSpec'.toInitFRNDEventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : InitFRNDEventSpec' AM M α) : InitFRNDEventSpec AM M α Unit :=
  {
    toInitNDEventSpec := ev.toInitNDEventSpec
    abstract := ev.abstract
    strengthening := ev.strengthening
    simulation := fun x => by
      simp
      intros Hgrd _ m' Hinit
      apply ev.simulation <;> assumption
  }

@[simp]
def newInitFRNDEvent' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : InitFRNDEventSpec' AM M α) : InitRNDEvent AM M α Unit :=
  newInitFRNDEvent ev.toInitFRNDEventSpec

structure InitFRNDEventSpec'' (AM) [Machine ACTX AM]
                        (M) [Machine CTX M]
                        [FRefinement AM M]
  extends InitNDEventSpec'' M where

  abstract : InitNDEvent AM Unit Unit

  strengthening:
    guard
    → abstract.guard Machine.reset ()

  simulation:
    guard
    → ∀ m', init m'
      → abstract.effect Machine.reset () ((), (lift m'))

@[simp]
def InitFRNDEventSpec''.toInitFRNDEventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : InitFRNDEventSpec'' AM M) : InitFRNDEventSpec AM M Unit Unit :=
  {
    toInitNDEventSpec := ev.toInitNDEventSpec
    abstract := ev.abstract
    strengthening := fun _ => ev.strengthening
    simulation := fun _ => by
      simp
      intros Hgrd _ m' Hinit
      apply ev.simulation <;> assumption
  }

@[simp]
def newInitFRNDEvent'' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : InitFRNDEventSpec'' AM M) : InitRNDEvent AM M Unit Unit :=
  newInitFRNDEvent ev.toInitFRNDEventSpec
