
import EventSystems.Refinement.Strong.NonDet.Det.Basic
import EventSystems.Refinement.Strong.NonDet.Convergent

import EventSystems.Refinement.Functional.NonDet.Det.Convergent

open Refinement
open FRefinement
open SRefinement


@[simp]
def newAnticipatedSRDetEventfromOrdinary [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryNDEvent AM α' β') (ev : AnticipatedRDetEventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : AnticipatedRDetEvent v AM M α β α' β' :=
  newAnticipatedRDetEventfromOrdinary abs ev

@[simp]
def newAnticipatedSRDetEventfromOrdinary' [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryNDEvent AM α' Unit) (ev : AnticipatedRDetEventSpec' v AM M (α:=α) (α':=α') abs) : AnticipatedRDetEvent v AM M α Unit α' Unit :=
  newAnticipatedSRDetEventfromOrdinary abs ev.toAnticipatedRDetEventSpec

@[simp]
def newAnticipatedSRDetEventfromOrdinary'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit) (ev : AnticipatedRDetEventSpec'' v AM M abs) : AnticipatedRDetEvent v AM M Unit Unit :=
  newAnticipatedSRDetEventfromOrdinary abs ev.toAnticipatedRDetEventSpec

@[simp]
def newAnticipatedSRDetEventfromAnticipated [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : AnticipatedNDEvent v AM α' β') (ev : AnticipatedRDetEventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs.toOrdinaryNDEvent) : AnticipatedRDetEvent v AM M α β α' β' :=
  newAnticipatedRDetEventfromAnticipated abs ev

@[simp]
def newAnticipatedSRDetEventfromAnticipated' [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : AnticipatedNDEvent v AM α' Unit) (ev : AnticipatedRDetEventSpec' v AM M (α:=α) (α':=α') abs.toOrdinaryNDEvent) : AnticipatedRDetEvent v AM M α Unit α' Unit :=
  newAnticipatedSRDetEventfromAnticipated abs ev.toAnticipatedRDetEventSpec

@[simp]
def newAnticipatedSRDetEventfromAnticipated'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : AnticipatedNDEvent v AM Unit Unit) (ev : AnticipatedRDetEventSpec'' v AM M abs.toOrdinaryNDEvent) : AnticipatedRDetEvent v AM M Unit Unit :=
  newAnticipatedSRDetEventfromAnticipated abs ev.toAnticipatedRDetEventSpec

@[simp]
def newConvergentSRDetEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryNDEvent AM α' β') (ev : ConvergentRDetEventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : ConvergentRDetEvent v AM M α β α' β' :=
  newConvergentRDetEvent abs ev

@[simp]
def newConvergentSRDetEvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryNDEvent AM α' Unit) (ev : ConvergentRDetEventSpec' v AM M (α:=α) (α':=α') abs) : ConvergentRDetEvent v AM M α Unit α' Unit :=
  newConvergentSRDetEvent abs ev.toConvergentRDetEventSpec

@[simp]
def newConvergentSRDetEvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit) (ev : ConvergentRDetEventSpec'' v AM M abs) : ConvergentRDetEvent v AM M Unit Unit :=
  newConvergentSRDetEvent abs ev.toConvergentRDetEventSpec
