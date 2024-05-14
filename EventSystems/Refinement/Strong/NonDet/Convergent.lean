import EventSystems.Refinement.Strong.Basic
import EventSystems.Refinement.Functional.NonDet.Convergent
import EventSystems.Event.Convergent

open Refinement
open FRefinement
open SRefinement

@[simp]
def newAnticipatedSRNDEventFromOrdinary [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryNDEvent AM α' β')
  (ev : AnticipatedRNDEventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs.to_NDEvent) : AnticipatedRNDEvent v AM M α β α' β' :=
  newAnticipatedRNDEventfromOrdinary abs ev

@[simp]
def newAnticipatedSRNDEventFromAnticipated [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : AnticipatedNDEvent v AM α' β')
  (ev : AnticipatedRNDEventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs.to_NDEvent) : AnticipatedRNDEvent v AM M α β α' β' :=
  newAnticipatedRNDEventfromAnticipated abs ev

@[simp]
def newConvergentSRNDEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : _NDEvent AM α' β') (ev : ConvergentRNDEventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : ConvergentRNDEvent v AM M α β α' β' :=
  newConvergentRNDEvent abs ev
