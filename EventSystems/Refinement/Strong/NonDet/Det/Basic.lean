
import EventSystems.Refinement.Strong.Basic
import EventSystems.Refinement.Functional.NonDet.Det.Basic

open Refinement
open FRefinement
open SRefinement

@[simp]
def newSRDetEvent [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryNDEvent AM α' β')
  (ev : FRDetEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs.to_NDEvent) : OrdinaryRDetEvent AM M α β α' β':=
  newRDetEvent abs ev.toRDetEventSpec

/- Initialization events -/

@[simp]
def newInitSRDetEvent [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : InitNDEvent AM α' β')
  (ev : InitFRDetEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : InitRDetEvent AM M α β α' β' :=
  newInitRDetEvent abs ev.toInitRDetEventSpec
