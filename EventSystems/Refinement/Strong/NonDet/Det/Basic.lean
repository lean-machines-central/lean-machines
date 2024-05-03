
import EventSystems.Refinement.Strong.Basic
import EventSystems.Refinement.Functional.NonDet.Det.Basic

open Refinement
open FRefinement
open SRefinement

structure SRDetEventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M] (α) (β)
  extends FRDetEventSpec AM M α β where

@[simp]
def newSRDetEvent [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : SRDetEventSpec AM M α β) : OrdinaryRDetEvent AM M α β :=
  newFRDetEvent ev.toFRDetEventSpec

structure SRDetEventSpec' (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M] (α)
  extends FRDetEventSpec' AM M α where

@[simp]
def newSRDetEvent' [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : SRDetEventSpec' AM M α) : OrdinaryRDetEvent AM M α Unit :=
  newFRDetEvent ev.toFRDetEventSpec

structure SRDetEventSpec'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M]
  extends FRDetEventSpec'' AM M where

@[simp]
def newSRDetEvent'' [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : SRDetEventSpec'' AM M) : OrdinaryRDetEvent AM M Unit Unit :=
  newFRDetEvent ev.toFRDetEventSpec

/- Initialization events -/

structure InitSRDetEventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M] (α) (β)
  extends InitFRDetEventSpec AM M α β where

@[simp]
def newInitSRDetEvent [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : InitSRDetEventSpec AM M α β) : InitRDetEvent AM M α β :=
  newInitFRDetEvent ev.toInitFRDetEventSpec

structure InitSRDetEventSpec' (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M] (α)
  extends InitFRDetEventSpec' AM M α where

@[simp]
def newInitSRDetEvent' [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : InitSRDetEventSpec' AM M α) : InitRDetEvent AM M α Unit :=
  newInitFRDetEvent ev.toInitFRDetEventSpec

structure InitSRDetEventSpec'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M]
  extends InitFRDetEventSpec'' AM M where

@[simp]
def newInitSRDetEvent'' [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : InitSRDetEventSpec'' AM M) : InitRDetEvent AM M Unit Unit :=
  newInitFRDetEvent ev.toInitFRDetEventSpec
