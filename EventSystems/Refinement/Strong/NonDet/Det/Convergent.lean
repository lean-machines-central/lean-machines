
import EventSystems.Refinement.Strong.NonDet.Det.Basic
import EventSystems.Refinement.Strong.NonDet.Convergent

import EventSystems.Refinement.Functional.NonDet.Det.Convergent

open Refinement
open FRefinement
open SRefinement


@[simp]
def newAnticipatedSRDetEventfromOrdinary [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryNDEvent AM α' β') (ev : AnticipatedRDetEventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs.to_NDEvent) : AnticipatedRDetEvent v AM M α β α' β' :=
  newAnticipatedRDetEventfromOrdinary abs ev

@[simp]
def newAnticipatedSRDetEventfromAnticipated [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : AnticipatedNDEvent v AM α' β') (ev : AnticipatedRDetEventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs.to_NDEvent) : AnticipatedRDetEvent v AM M α β α' β' :=
  newAnticipatedRDetEventfromAnticipated abs ev

@[simp]
def newConvergentSRDetEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : _NDEvent AM α' β') (ev : ConvergentRDetEventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : ConvergentRDetEvent v AM M α β α' β' :=
  newConvergentRDetEvent abs ev
