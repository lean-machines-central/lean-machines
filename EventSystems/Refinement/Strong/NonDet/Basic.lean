
import EventSystems.NonDet.Basic
import EventSystems.NonDet.Ordinary
import EventSystems.Refinement.Functional.NonDet.Basic
import EventSystems.Refinement.Strong.Basic

open Refinement
open FRefinement
open SRefinement

structure SRNDEventSpec (AM) [Machine ACTX AM]
                        (M) [Machine CTX M]
                        [SRefinement AM M] (α) (β)
  extends FRNDEventSpec AM M α β where

@[simp]
def newSRNDEvent [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : SRNDEventSpec AM M α β) : OrdinaryRNDEvent AM M α β :=
  newFRNDEvent ev.toFRNDEventSpec

structure SRNDEventSpec' (AM) [Machine ACTX AM]
                        (M) [Machine CTX M]
                        [SRefinement AM M] (α)
  extends FRNDEventSpec' AM M α where

@[simp]
def newSRNDEvent' [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : SRNDEventSpec' AM M α) : OrdinaryRNDEvent AM M α Unit :=
  newFRNDEvent ev.toFRNDEventSpec

structure SRNDEventSpec'' (AM) [Machine ACTX AM]
                          (M) [Machine CTX M]
                          [SRefinement AM M]
  extends FRNDEventSpec'' AM M where

@[simp]
def newSRNDEvent'' [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : SRNDEventSpec'' AM M) : OrdinaryRNDEvent AM M Unit Unit :=
  newFRNDEvent ev.toFRNDEventSpec

structure InitSRNDEventSpec (AM) [Machine ACTX AM]
                        (M) [Machine CTX M]
                        [SRefinement AM M] (α) (β)
  extends InitFRNDEventSpec AM M α β where

@[simp]
def newInitSRNDEvent [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : InitSRNDEventSpec AM M α β) : InitRNDEvent AM M α β :=
  newInitFRNDEvent ev.toInitFRNDEventSpec

structure InitSRNDEventSpec' (AM) [Machine ACTX AM]
                        (M) [Machine CTX M]
                        [SRefinement AM M] (α)
  extends InitFRNDEventSpec' AM M α where

@[simp]
def newInitSRNDEvent' [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : InitSRNDEventSpec' AM M α) : InitRNDEvent AM M α Unit :=
  newInitFRNDEvent ev.toInitFRNDEventSpec

structure InitSRNDEventSpec'' (AM) [Machine ACTX AM]
                        (M) [Machine CTX M]
                        [SRefinement AM M]
  extends InitFRNDEventSpec'' AM M where

@[simp]
def newInitSRNDEvent'' [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : InitSRNDEventSpec'' AM M) : InitRNDEvent AM M Unit Unit :=
  newInitFRNDEvent ev.toInitFRNDEventSpec
