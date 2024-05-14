
import EventSystems.Refinement.Functional.Basic
import EventSystems.Refinement.Relational.Convergent
import EventSystems.Event.Convergent

open Refinement
open FRefinement

@[simp]
def newAnticipatedFREventfromOrdinary [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM α' β') (ev : AnticipatedREventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs.to_Event) : AnticipatedREvent v AM M α β α' β' :=
  newAnticipatedREventfromOrdinary abs ev

@[simp]
def newAnticipatedFREventfromAnticipated [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : AnticipatedEvent v AM α' β') (ev : AnticipatedREventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs.to_Event) : AnticipatedREvent v AM M α β α' β' :=
  newAnticipatedREventfromAnticipated abs ev

@[simp]
def newConvergentFREvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : _Event AM α' β') (ev : ConvergentREventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : ConvergentREvent v AM M α β α' β' :=
  newConvergentREvent abs ev
