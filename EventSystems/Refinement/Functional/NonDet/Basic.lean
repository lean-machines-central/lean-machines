
import EventSystems.NonDet.Basic
import EventSystems.NonDet.Ordinary
import EventSystems.Refinement.Relational.NonDet.Basic
import EventSystems.Refinement.Functional.Basic

open Refinement
open FRefinement

structure _FRNDEventSpec (AM) [Machine ACTX AM]
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
def _FRNDEventSpec.to_RNDEventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  {α β α' β'} (abs : _NDEvent AM α' β')
  (ev : _FRNDEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : _RNDEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs :=
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

structure FRNDEventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M]
  {α β α' β'} (abstract : OrdinaryNDEvent AM α' β')
  extends _FRNDEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abstract.to_NDEvent where

@[simp]
def FRNDEventSpec.toRNDEventSpec [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  {α β α' β'} (abs : OrdinaryNDEvent AM α' β')
  (ev : FRNDEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : RNDEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs :=
  {
    to_RNDEventSpec := ev.to_RNDEventSpec
  }

@[simp]
def newFRNDEvent [Machine ACTX AM] [Machine CTX M] [instFR:FRefinement AM M]
  (abs : OrdinaryNDEvent AM α' β') (ev : FRNDEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : OrdinaryRNDEvent AM M α β α' β' :=
  newRNDEvent abs ev.toRNDEventSpec

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
