
import EventSystems.Refinement.Functional.Basic
import EventSystems.NonDet.Ordinary
import EventSystems.Refinement.Relational.NonDet.Det.Basic

open Refinement
open FRefinement

structure FRDetEventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M]
  {α β α' β'} (abstract : _NDEvent AM α' β')
  extends EventSpec M α β where

  lift_in : α → α'
  lift_out : β → β'

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → abstract.guard (lift m) (lift_in x)

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let (y, m') := action m x
      abstract.effect (lift m) (lift_in x) (lift_out y, lift m')

@[simp]
def FRDetEventSpec.toRDetEventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (abstract : _NDEvent AM α' β') (ev : FRDetEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abstract) : RDetEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abstract :=
  {
    toEventSpec := ev.toEventSpec
    lift_in := ev.lift_in
    lift_out := ev.lift_out

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
  (abs : OrdinaryNDEvent AM α' β')
  (ev : FRDetEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs.to_NDEvent) : OrdinaryRDetEvent AM M α β α' β':=
  newRDetEvent abs ev.toRDetEventSpec

/- Initialization events -/

structure InitFRDetEventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M]
  {α β α' β'} (abstract : InitNDEvent AM α' β')
  extends InitEventSpec M α β where

  lift_in : α → α'
  lift_out : β → β'

  strengthening (x : α):
    guard x
    → abstract.guard Machine.reset (lift_in x)

  simulation (x : α):
    guard x
    → let (y, m') := init x
      abstract.effect Machine.reset (lift_in x) (lift_out y, lift m')

@[simp]
def InitFRDetEventSpec.toInitRDetEventSpec  [Machine ACTX AM] [Machine CTX M] [instFR:FRefinement AM M]
  (abstract : InitNDEvent AM α' β')
  (ev : InitFRDetEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abstract) : InitRDetEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abstract :=
  {
    toInitEventSpec := ev.toInitEventSpec
    lift_in := ev.lift_in
    lift_out := ev.lift_out
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
  (abs : InitNDEvent AM α' β')
  (ev : InitFRDetEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : InitRDetEvent AM M α β α' β' :=
  newInitRDetEvent abs ev.toInitRDetEventSpec
