
import LeanMachines.Refinement.Strong.Basic
import LeanMachines.Refinement.Functional.NonDet.Det.Basic

open Refinement
open FRefinement
open SRefinement

@[simp]
def newSRDetEvent [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryNDEvent AM α' β')
  (ev : FRDetEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : OrdinaryRDetEvent AM M α β α' β':=
  newRDetEvent abs ev.toRDetEventSpec

@[simp]
def newSRDetEvent' [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryNDEvent AM α' Unit)
  (ev : FRDetEventSpec' AM M (α:=α) (α':=α') abs) : OrdinaryRDetEvent AM M α Unit α' Unit:=
  newSRDetEvent abs ev.toFRDetEventSpec

@[simp]
def newSRDetEvent'' [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit)
  (ev : FRDetEventSpec'' AM M abs) : OrdinaryRDetEvent AM M Unit Unit:=
  newSRDetEvent abs ev.toFRDetEventSpec

/- Initialization events -/

@[simp]
def newInitSRDetEvent [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : InitNDEvent AM α' β')
  (ev : InitFRDetEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : InitRDetEvent AM M α β α' β' :=
  newInitRDetEvent abs ev.toInitRDetEventSpec

@[simp]
def newInitSRDetEvent' [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : InitNDEvent AM α' Unit)
  (ev : InitFRDetEventSpec' AM M (α:=α) (α':=α') abs) : InitRDetEvent AM M α Unit α' Unit :=
  newInitSRDetEvent abs ev.toInitFRDetEventSpec

@[simp]
def newInitSRDetEvent'' [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : InitNDEvent AM Unit Unit)
  (ev : InitFRDetEventSpec'' AM M abs) : InitRDetEvent AM M Unit Unit :=
  newInitSRDetEvent abs ev.toInitFRDetEventSpec
