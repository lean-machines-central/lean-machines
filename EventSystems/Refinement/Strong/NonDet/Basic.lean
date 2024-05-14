
import EventSystems.NonDet.Basic
import EventSystems.NonDet.Ordinary
import EventSystems.Refinement.Functional.NonDet.Basic
import EventSystems.Refinement.Strong.Basic

open Refinement
open FRefinement
open SRefinement

@[simp]
def newSRNDEvent [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
(abs : OrdinaryNDEvent AM α' β') (ev : FRNDEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs.to_NDEvent) : OrdinaryRNDEvent AM M α β α' β' :=
  newRNDEvent abs ev.toRNDEventSpec

@[simp]
def newInitSRNDEvent [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : InitNDEvent AM α' β') (ev : InitFRNDEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : InitRNDEvent AM M α β α' β' :=
  newInitRNDEvent abs ev.toInitRNDEventSpec
