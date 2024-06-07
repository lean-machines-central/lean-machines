import LeanMachines.Refinement.Strong.Basic
import LeanMachines.Refinement.Functional.NonDet.Convergent
import LeanMachines.Event.Convergent

open Refinement
open FRefinement
open SRefinement

@[simp]
def newAnticipatedSRNDEventFromOrdinary [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryNDEvent AM α' β')
  (ev : AnticipatedRNDEventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : AnticipatedRNDEvent v AM M α β α' β' :=
  newAnticipatedRNDEventfromOrdinary abs ev

@[simp]
def newAnticipatedSRNDEventFromOrdinary' [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryNDEvent AM α' Unit)
  (ev : AnticipatedRNDEventSpec' v AM M (α:=α) (α':=α') abs) : AnticipatedRNDEvent v AM M α Unit α' Unit :=
   newAnticipatedSRNDEventFromOrdinary abs ev.toAnticipatedRNDEventSpec

@[simp]
def newAnticipatedSRNDEventFromOrdinary'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit)
  (ev : AnticipatedRNDEventSpec'' v AM M abs) : AnticipatedRNDEvent v AM M Unit Unit :=
   newAnticipatedSRNDEventFromOrdinary abs ev.toAnticipatedRNDEventSpec

@[simp]
def newAnticipatedSRNDEventFromAnticipated [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : AnticipatedNDEvent v AM α' β')
  (ev : AnticipatedRNDEventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs.toOrdinaryNDEvent) : AnticipatedRNDEvent v AM M α β α' β' :=
  newAnticipatedRNDEventfromAnticipated abs ev

@[simp]
def newAnticipatedSRNDEventFromAnticipated' [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : AnticipatedNDEvent v AM α' Unit)
  (ev : AnticipatedRNDEventSpec' v AM M (α:=α) (α':=α') abs.toOrdinaryNDEvent) : AnticipatedRNDEvent v AM M α Unit α' Unit :=
  newAnticipatedSRNDEventFromAnticipated abs ev.toAnticipatedRNDEventSpec

@[simp]
def newAnticipatedSRNDEventFromAnticipated'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : AnticipatedNDEvent v AM Unit Unit)
  (ev : AnticipatedRNDEventSpec'' v AM M abs.toOrdinaryNDEvent) : AnticipatedRNDEvent v AM M Unit Unit :=
  newAnticipatedSRNDEventFromAnticipated abs ev.toAnticipatedRNDEventSpec

@[simp]
def newConvergentSRNDEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryNDEvent AM α' β') (ev : ConvergentRNDEventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : ConvergentRNDEvent v AM M α β α' β' :=
  newConvergentRNDEvent abs ev

@[simp]
def newConvergentSRNDEvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryNDEvent AM α' Unit) (ev : ConvergentRNDEventSpec' v AM M (α:=α) (α':=α') abs) : ConvergentRNDEvent v AM M α Unit α' Unit :=
  newConvergentSRNDEvent abs ev.toConvergentRNDEventSpec

@[simp]
def newConvergentSRNDEvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit) (ev : ConvergentRNDEventSpec'' v AM M abs) : ConvergentRNDEvent v AM M Unit Unit :=
  newConvergentSRNDEvent abs ev.toConvergentRNDEventSpec
