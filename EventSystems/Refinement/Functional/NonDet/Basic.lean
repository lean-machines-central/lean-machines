
import EventSystems.NonDet.Basic
import EventSystems.NonDet.Ordinary
import EventSystems.Refinement.Relational.NonDet.Basic
import EventSystems.Refinement.Functional.Basic

open Refinement
open FRefinement

structure FRNDEventSpec (AM) [Machine ACTX AM]
                         (M) [Machine CTX M]
                         [FRefinement AM M]
  {α β α' β'} (abstract : _NDEvent AM α' β')
  extends NDEventSpec M α β where

  lift_in : α → α'
  lift_out : β → β'

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → abstract.guard (lift m) (lift_in x)

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ y, ∀ m', effect m x (y, m')
      → abstract.effect (lift m) (lift_in x) (lift_out y, (lift m'))

@[simp]
def FRNDEventSpec.toRNDEventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  {α β α' β'} (abs : _NDEvent AM α' β')
  (ev : FRNDEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : RNDEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs :=
  {
    toNDEventSpec := ev.toNDEventSpec

    lift_in := ev.lift_in
    lift_out := ev.lift_out

    strengthening := fun m x => by
      intros Hinv Hgrd am Href
      have Hst := ev.strengthening m x Hinv Hgrd
      have Href' := lift_ref (self:=instFR) m Hinv
      have Huniq := refine_uniq (self:=instFR) am (lift m) m Hinv Href Href'
      rw [Huniq]
      exact Hst

    simulation := fun m x => by
      intros Hinv Hgrd y m' Heff am Href
      exists (lift m')
      have Hsim := ev.simulation m x Hinv Hgrd y m' Heff
      have Href' := lift_ref (self:=instFR) m Hinv
      have Huniq := refine_uniq (self:=instFR) am (lift m) m Hinv Href Href'
      rw [Huniq]
      simp [Hsim]
      have Hsafe := ev.safety m x Hinv Hgrd y m' Heff
      apply lift_ref (self:=instFR) m' Hsafe
  }

@[simp]
def newFRNDEvent [Machine ACTX AM] [Machine CTX M] [instFR:FRefinement AM M]
  (abs : OrdinaryNDEvent AM α' β') (ev : FRNDEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs.to_NDEvent) : OrdinaryRNDEvent AM M α β α' β' :=
  newRNDEvent abs ev.toRNDEventSpec

structure FRNDEventSpec' (AM) [Machine ACTX AM]
                         (M) [Machine CTX M]
                         [FRefinement AM M]
  {α α'} (abstract : _NDEvent AM α' Unit)
  extends NDEventSpec' M α where

  lift_in : α → α'

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → abstract.guard (lift m) (lift_in x)

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ m', effect m x m'
      → abstract.effect (lift m) (lift_in x) ((), (lift m'))

@[simp]
def FRNDEventSpec'.toFRNDEventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  {α α'} (abs : _NDEvent AM α' Unit)
  (ev : FRNDEventSpec' AM M (α:=α) (α':=α') abs) : FRNDEventSpec AM M (α:=α) (β:=Unit) (α':=α') (β':=Unit) abs :=
  {
    toNDEventSpec := ev.toNDEventSpec
    lift_in := ev.lift_in
    lift_out := id
    strengthening := ev.strengthening
    simulation := fun m x => by
      simp
      intros Hinv Hgrd _ m' Heff
      apply ev.simulation m x <;> assumption
  }

@[simp]
def newFRNDEvent' [Machine ACTX AM] [Machine CTX M] [instFR:FRefinement AM M]
  (abs : OrdinaryNDEvent AM α' Unit) (ev : FRNDEventSpec' AM M (α:=α) (α':=α') abs.to_NDEvent) : OrdinaryRNDEvent AM M α Unit α' Unit :=
  newFRNDEvent abs ev.toFRNDEventSpec

structure FRNDEventSpec'' (AM) [Machine ACTX AM]
                         (M) [Machine CTX M]
                         [FRefinement AM M]
  (abstract : _NDEvent AM Unit Unit)
  extends NDEventSpec'' M where

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
def FRNDEventSpec''.toFRNDEventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (abs : _NDEvent AM Unit Unit)
  (ev : FRNDEventSpec'' AM M abs) : FRNDEventSpec AM M (α:=Unit) (β:=Unit) (α':=Unit) (β':=Unit) abs :=
  {
    toNDEventSpec := ev.toNDEventSpec
    lift_in := id
    lift_out := id
    strengthening := fun m () => ev.strengthening m
    simulation := fun m () => by
      simp
      intros Hinv Hgrd _ m' Heff
      apply ev.simulation m <;> assumption
  }

@[simp]
def newFRNDEvent'' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit) (ev : FRNDEventSpec'' AM M abs.to_NDEvent) : OrdinaryRNDEvent AM M Unit Unit :=
  newFRNDEvent abs ev.toFRNDEventSpec

/- Initialization events -/

structure InitFRNDEventSpec (AM) [Machine ACTX AM]
                        (M) [Machine CTX M]
                        [FRefinement AM M]
  {α β α' β'} (abstract : InitNDEvent AM α' β')
  extends InitNDEventSpec M α β where

  lift_in : α → α'
  lift_out : β → β'

  strengthening (x : α):
    guard x
    → abstract.guard Machine.reset (lift_in x)

  simulation (x : α):
    guard x
    → ∀ y, ∀ m', init x (y, m')
      → abstract.effect Machine.reset (lift_in x) (lift_out y, (lift m'))

@[simp]
def InitFRNDEventSpec.toInitRNDEventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  {α β α' β'} (abs : InitNDEvent AM α' β')
  (ev : InitFRNDEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : InitRNDEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs :=
  {
    toInitNDEventSpec := ev.toInitNDEventSpec
    lift_in := ev.lift_in
    lift_out := ev.lift_out
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
  (abs : InitNDEvent AM α' β')
  (ev : InitFRNDEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : InitRNDEvent AM M α β α' β' :=
  newInitRNDEvent abs ev.toInitRNDEventSpec

structure InitFRNDEventSpec' (AM) [Machine ACTX AM]
                        (M) [Machine CTX M]
                        [FRefinement AM M]
  {α α'} (abstract : InitNDEvent AM α' Unit)
  extends InitNDEventSpec' M α where

  lift_in : α → α'

  strengthening (x : α):
    guard x
    → abstract.guard Machine.reset (lift_in x)

  simulation (x : α):
    guard x
    → ∀ m', init x m'
      → abstract.effect Machine.reset (lift_in x) ((), (lift m'))

@[simp]
def InitFRNDEventSpec'.toInitFRNDEventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  {α α'} (abs : InitNDEvent AM α' Unit)
  (ev : InitFRNDEventSpec' AM M (α:=α) (α':=α') abs) : InitFRNDEventSpec AM M (α:=α) (β:=Unit) (α':=α') (β':=Unit) abs :=
  {
    toInitNDEventSpec := ev.toInitNDEventSpec
    lift_in := ev.lift_in
    lift_out := id
    strengthening := ev.strengthening
    simulation := fun x => by
      simp
      intros Hgrd _ m' Hini
      apply ev.simulation x <;> assumption
  }

@[simp]
def newInitFRNDEvent' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : InitNDEvent AM α' Unit)
  (ev : InitFRNDEventSpec' AM M (α:=α) (α':=α') abs) : InitRNDEvent AM M α Unit α' Unit :=
  newInitFRNDEvent abs ev.toInitFRNDEventSpec

structure InitFRNDEventSpec'' (AM) [Machine ACTX AM]
                        (M) [Machine CTX M]
                        [FRefinement AM M]
  (abstract : InitNDEvent AM Unit Unit)
  extends InitNDEventSpec'' M where

  strengthening:
    guard
    → abstract.guard Machine.reset ()

  simulation:
    guard
    → ∀ m', init m'
      → abstract.effect Machine.reset () ((), (lift m'))

@[simp]
def InitFRNDEventSpec''.toInitFRNDEventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (abs : InitNDEvent AM Unit Unit)
  (ev : InitFRNDEventSpec'' AM M abs) : InitFRNDEventSpec AM M (α:=Unit) (β:=Unit) (α':=Unit) (β':=Unit) abs :=
  {
    toInitNDEventSpec := ev.toInitNDEventSpec
    lift_in := id
    lift_out := id
    strengthening := fun _ => ev.strengthening
    simulation := fun _ => by
      simp
      intros Hgrd _ m' Hini
      apply ev.simulation <;> assumption
  }

@[simp]
def newInitFRNDEvent'' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : InitNDEvent AM Unit Unit)
  (ev : InitFRNDEventSpec'' AM M abs) : InitRNDEvent AM M Unit Unit :=
  newInitFRNDEvent abs ev.toInitFRNDEventSpec
