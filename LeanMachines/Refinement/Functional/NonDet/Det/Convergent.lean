
import LeanMachines.NonDet.Basic

import LeanMachines.Refinement.Functional.NonDet.Det.Basic
import LeanMachines.Refinement.Functional.NonDet.Convergent

import LeanMachines.Refinement.Relational.NonDet.Det.Convergent

open Refinement
open FRefinement

@[simp]
def newAnticipatedFRDetEventfromOrdinary [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryNDEvent AM α' β') (ev : AnticipatedRDetEventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : AnticipatedRDetEvent v AM M α β α' β' :=
  newAnticipatedRDetEventfromOrdinary abs ev

@[simp]
def newAnticipatedFRDetEventfromOrdinary' [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryNDEvent AM α' Unit) (ev : AnticipatedRDetEventSpec' v AM M (α:=α) (α':=α') abs) : AnticipatedRDetEvent v AM M α Unit α' Unit :=
  newAnticipatedFRDetEventfromOrdinary abs ev.toAnticipatedRDetEventSpec

@[simp]
def newAnticipatedFRDetEventfromOrdinary'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit) (ev : AnticipatedRDetEventSpec'' v AM M abs) : AnticipatedRDetEvent v AM M Unit Unit :=
  newAnticipatedFRDetEventfromOrdinary abs ev.toAnticipatedRDetEventSpec

@[simp]
def newAnticipatedFRDetEventfromAnticipated [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : AnticipatedNDEvent v AM α' β') (ev : AnticipatedRDetEventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs.toOrdinaryNDEvent) : AnticipatedRDetEvent v AM M α β α' β' :=
  newAnticipatedRDetEventfromAnticipated abs ev

@[simp]
def newAnticipatedFRDetEventfromAnticipated' [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : AnticipatedNDEvent v AM α' Unit) (ev : AnticipatedRDetEventSpec' v AM M (α:=α) (α':=α') abs.toOrdinaryNDEvent) : AnticipatedRDetEvent v AM M α Unit α' Unit :=
  newAnticipatedFRDetEventfromAnticipated abs ev.toAnticipatedRDetEventSpec

@[simp]
def newAnticipatedFRDetEventfromAnticipated'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : AnticipatedNDEvent v AM Unit Unit) (ev : AnticipatedRDetEventSpec'' v AM M abs.toOrdinaryNDEvent) : AnticipatedRDetEvent v AM M Unit Unit :=
  newAnticipatedFRDetEventfromAnticipated abs ev.toAnticipatedRDetEventSpec

@[simp]
def newConvergentFRDetEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryNDEvent AM α' β') (ev : ConvergentRDetEventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : ConvergentRDetEvent v AM M α β α' β' :=
  newConvergentRDetEvent abs ev

@[simp]
def newConvergentFRDetEvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryNDEvent AM α' Unit) (ev : ConvergentRDetEventSpec' v AM M (α:=α) (α':=α') abs) : ConvergentRDetEvent v AM M α Unit α' Unit :=
  newConvergentFRDetEvent abs ev.toConvergentRDetEventSpec

@[simp]
def newConvergentFRDetEvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit) (ev : ConvergentRDetEventSpec'' v AM M abs) : ConvergentRDetEvent v AM M Unit Unit :=
  newConvergentFRDetEvent abs ev.toConvergentRDetEventSpec
