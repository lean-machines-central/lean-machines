
import EventSystems.NonDet.Basic
import EventSystems.NonDet.Ordinary
import EventSystems.Refinement.Functional.NonDet.Basic
import EventSystems.Refinement.Strong.Basic

open Refinement
open FRefinement
open SRefinement

@[simp]
def newSRNDEvent [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
(abs : OrdinaryNDEvent AM α' β') (ev : FRNDEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : OrdinaryRNDEvent AM M α β α' β' :=
  newRNDEvent abs ev.toRNDEventSpec

@[simp]
def newSRNDEvent' [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
(abs : OrdinaryNDEvent AM α' Unit) (ev : FRNDEventSpec' AM M (α:=α) (α':=α') abs) : OrdinaryRNDEvent AM M α Unit α' Unit :=
  newSRNDEvent abs ev.toFRNDEventSpec

@[simp]
def newSRNDEvent'' [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
(abs : OrdinaryNDEvent AM Unit Unit) (ev : FRNDEventSpec'' AM M abs) : OrdinaryRNDEvent AM M Unit Unit :=
  newSRNDEvent abs ev.toFRNDEventSpec

@[simp]
def newInitSRNDEvent [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : InitNDEvent AM α' β') (ev : InitFRNDEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : InitRNDEvent AM M α β α' β' :=
  newInitRNDEvent abs ev.toInitRNDEventSpec

@[simp]
def newInitSRNDEvent' [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : InitNDEvent AM α' Unit) (ev : InitFRNDEventSpec' AM M (α:=α) (α':=α') abs) : InitRNDEvent AM M α Unit α' Unit :=
  newInitSRNDEvent abs ev.toInitFRNDEventSpec

@[simp]
def newInitSRNDEvent'' [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : InitNDEvent AM Unit Unit) (ev : InitFRNDEventSpec'' AM M abs) : InitRNDEvent AM M Unit Unit :=
  newInitSRNDEvent abs ev.toInitFRNDEventSpec
