
import EventSystems.NonDet.Basic

import EventSystems.Refinement.Functional.NonDet.Det.Basic
import EventSystems.Refinement.Functional.NonDet.Convergent

import EventSystems.Refinement.Relational.NonDet.Det.Convergent

open Refinement
open FRefinement

@[simp]
def newAnticipatedFRDetEventfromOrdinary [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryNDEvent AM α' β') (ev : AnticipatedRDetEventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs.to_NDEvent) : AnticipatedRDetEvent v AM M α β α' β' :=
  newAnticipatedRDetEventfromOrdinary abs ev

@[simp]
def newAnticipatedFRDetEventfromAnticipated [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : AnticipatedNDEvent v AM α' β') (ev : AnticipatedRDetEventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs.to_NDEvent) : AnticipatedRDetEvent v AM M α β α' β' :=
  newAnticipatedRDetEventfromAnticipated abs ev

@[simp]
def newConvergentFRDetEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : _NDEvent AM α' β') (ev : ConvergentRDetEventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : ConvergentRDetEvent v AM M α β α' β' :=
  newConvergentRDetEvent abs ev
