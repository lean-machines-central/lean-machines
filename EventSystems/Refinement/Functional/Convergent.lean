
import EventSystems.Refinement.Functional.Basic
import EventSystems.Refinement.Relational.Convergent
import EventSystems.Event.Convergent

open Refinement
open FRefinement

structure AnticipatedFREventSpecFromOrdinary (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M]
  {α β α' β'} (abs : OrdinaryEvent AM α' β')
  extends AnticipatedREventSpecFromOrdinary v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs where

@[simp]
def newAnticipatedFREventfromOrdinary [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM α' β') (ev : AnticipatedFREventSpecFromOrdinary v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : AnticipatedREvent v AM M α β α' β' :=
  newAnticipatedREventfromOrdinary abs ev.toAnticipatedREventSpecFromOrdinary

structure AnticipatedFREventSpecFromAnticipated (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M]
  {α β α' β'} (abs : AnticipatedEvent v AM α' β')
  extends AnticipatedREventSpecFromAnticipated v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs where

@[simp]
def newAnticipatedFREventfromAnticipated [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : AnticipatedEvent v AM α' β') (ev : AnticipatedFREventSpecFromAnticipated v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : AnticipatedREvent v AM M α β α' β' :=
  newAnticipatedREventfromAnticipated abs ev.toAnticipatedREventSpecFromAnticipated


structure ConvergentFREventSpec (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M]
  {α β α' β'} (abs : _Event AM α' β')
  extends ConvergentREventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs where

@[simp]
def newConvergentFREvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : _Event AM α' β') (ev : ConvergentFREventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : ConvergentREvent v AM M α β α' β' :=
  newConvergentREvent abs ev.toConvergentREventSpec
