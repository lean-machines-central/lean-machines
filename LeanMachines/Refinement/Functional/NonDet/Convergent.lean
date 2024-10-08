
import LeanMachines.Refinement.Functional.NonDet.Basic
import LeanMachines.Refinement.Relational.NonDet.Convergent

open Refinement
open FRefinement

@[simp]
def newAnticipatedFRNDEventfromOrdinary [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryNDEvent AM α' β')
  (ev : AnticipatedRNDEventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : AnticipatedRNDEvent v AM M α β α' β' :=
  newAnticipatedRNDEventfromOrdinary abs ev

@[simp]
def newAnticipatedFRNDEventfromOrdinary' [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryNDEvent AM α' Unit)
  (ev : AnticipatedRNDEventSpec' v AM M (α:=α) (α':=α') abs) : AnticipatedRNDEvent v AM M α Unit α' Unit :=
  newAnticipatedRNDEventfromOrdinary abs ev.toAnticipatedRNDEventSpec

@[simp]
def newAnticipatedFRNDEventfromOrdinary'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit)
  (ev : AnticipatedRNDEventSpec'' v AM M abs) : AnticipatedRNDEvent v AM M Unit Unit :=
  newAnticipatedRNDEventfromOrdinary abs ev.toAnticipatedRNDEventSpec

@[simp]
def newAnticipatedFRNDEventfromAnticipated [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : AnticipatedNDEvent v AM α' β') (ev : AnticipatedRNDEventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs.toOrdinaryNDEvent) : AnticipatedRNDEvent v AM M α β α' β' :=
  newAnticipatedRNDEventfromAnticipated abs ev

@[simp]
def newAnticipatedFRNDEventfromAnticipated' [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : AnticipatedNDEvent v AM α' Unit) (ev : AnticipatedRNDEventSpec' v AM M (α:=α) (α':=α') abs.toOrdinaryNDEvent) : AnticipatedRNDEvent v AM M α Unit α' Unit :=
  newAnticipatedRNDEventfromAnticipated abs ev.toAnticipatedRNDEventSpec

@[simp]
def newAnticipatedFRNDEventfromAnticipated'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : AnticipatedNDEvent v AM Unit Unit) (ev : AnticipatedRNDEventSpec'' v AM M abs.toOrdinaryNDEvent) : AnticipatedRNDEvent v AM M Unit Unit :=
  newAnticipatedRNDEventfromAnticipated abs ev.toAnticipatedRNDEventSpec

@[simp]
def newConvergentFRNDEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryNDEvent AM α' β') (ev : ConvergentRNDEventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : ConvergentRNDEvent v AM M α β α' β' :=
  newConvergentRNDEvent abs ev

@[simp]
def newConvergentFRNDEvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryNDEvent AM α' Unit) (ev : ConvergentRNDEventSpec' v AM M (α:=α) (α':=α') abs) : ConvergentRNDEvent v AM M α Unit α' Unit :=
  newConvergentRNDEvent abs ev.toConvergentRNDEventSpec

@[simp]
def newConvergentFRNDEvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit) (ev : ConvergentRNDEventSpec'' v AM M abs) : ConvergentRNDEvent v AM M Unit Unit :=
  newConvergentRNDEvent abs ev.toConvergentRNDEventSpec
