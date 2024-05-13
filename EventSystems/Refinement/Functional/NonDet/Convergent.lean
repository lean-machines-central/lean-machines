
import EventSystems.Refinement.Functional.NonDet.Basic
import EventSystems.Refinement.Relational.NonDet.Convergent

open Refinement
open FRefinement

structure AnticipatedFREventSpecFromOrdinary (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M]
  {α β α' β'} (abs : OrdinaryNDEvent AM α' β')
  extends AnticipatedRNDEventSpecFromOrdinary v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs where

@[simp]
def newAnticipatedFRNDEventfromOrdinary [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryNDEvent AM α' β')
  (ev : AnticipatedFREventSpecFromOrdinary v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : AnticipatedRNDEvent v AM M α β α' β' :=
  newAnticipatedRNDEventfromOrdinary abs ev.toAnticipatedRNDEventSpecFromOrdinary

structure AnticipatedFRNDEventSpecFromAnticipated (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M]
  {α β α' β'} (abs : AnticipatedNDEvent v AM α' β')
  extends AnticipatedRNDEventSpecFromAnticipated v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs where

@[simp]
def newAnticipatedFRNDEventfromAnticipated [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : AnticipatedNDEvent v AM α' β') (ev : AnticipatedFRNDEventSpecFromAnticipated v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : AnticipatedRNDEvent v AM M α β α' β' :=
  newAnticipatedRNDEventfromAnticipated abs ev.toAnticipatedRNDEventSpecFromAnticipated


structure ConvergentFRNDEventSpec (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M]
  {α β α' β'} (abs : _NDEvent AM α' β')
  extends ConvergentRNDEventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs where

@[simp]
def newConvergentFREvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : _NDEvent AM α' β') (ev : ConvergentFRNDEventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : ConvergentRNDEvent v AM M α β α' β' :=
  newConvergentRNDEvent abs ev.toConvergentRNDEventSpec
