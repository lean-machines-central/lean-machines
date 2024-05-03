
import EventSystems.Refinement.Strong.NonDet.Det.Basic
import EventSystems.Refinement.Strong.NonDet.Convergent

import EventSystems.Refinement.Functional.NonDet.Det.Convergent

open Refinement
open FRefinement
open SRefinement

structure AnticipatedSRDetEventSpec_fromOrdinary (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M] (α) (β)
  extends AnticipatedFRDetEventSpec_fromOrdinary v AM M α β where

@[simp]
def newAnticipatedSRDetEvent_fromOrdinary [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : AnticipatedSRDetEventSpec_fromOrdinary v AM M α β) : AnticipatedRDetEvent v AM M α β :=
  newAnticipatedFRDetEvent_fromOrdinary ev.toAnticipatedFRDetEventSpec_fromOrdinary

structure AnticipatedSRDetEventSpec_fromOrdinary' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M] (α)
  extends AnticipatedFRDetEventSpec_fromOrdinary' v AM M α where

@[simp]
def newAnticipatedSRDetEvent_fromOrdinary' [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : AnticipatedSRDetEventSpec_fromOrdinary' v AM M α) : AnticipatedRDetEvent v AM M α Unit :=
  newAnticipatedFRDetEvent_fromOrdinary ev.toAnticipatedFRDetEventSpec_fromOrdinary

structure AnticipatedSRDetEventSpec_fromOrdinary'' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M]
  extends AnticipatedFRDetEventSpec_fromOrdinary'' v AM M where

@[simp]
def newAnticipatedSRDetEvent_fromOrdinary'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : AnticipatedSRDetEventSpec_fromOrdinary'' v AM M) : AnticipatedRDetEvent v AM M Unit Unit :=
  newAnticipatedFRDetEvent_fromOrdinary ev.toAnticipatedFRDetEventSpec_fromOrdinary

structure AnticipatedSRDetEventSpec_fromAnticipated (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M] (α) (β)
  extends AnticipatedFRDetEventSpec_fromAnticipated v AM M α β where

@[simp]
def newAnticipatedSRDetEvent_fromAnticipated [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : AnticipatedSRDetEventSpec_fromAnticipated v AM M α β) : AnticipatedRDetEvent v AM M α β :=
  newAnticipatedFRDetEvent_fromAnticipated ev.toAnticipatedFRDetEventSpec_fromAnticipated

structure AnticipatedSRDetEventSpec_fromAnticipated' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M] (α)
  extends AnticipatedFRDetEventSpec_fromAnticipated' v AM M α where

@[simp]
def newAnticipatedSRDetEvent_fromAnticipated' [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : AnticipatedSRDetEventSpec_fromAnticipated' v AM M α) : AnticipatedRDetEvent v AM M α Unit :=
  newAnticipatedFRDetEvent_fromAnticipated ev.toAnticipatedFRDetEventSpec_fromAnticipated

structure AnticipatedSRDetEventSpec_fromAnticipated'' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M]
  extends AnticipatedFRDetEventSpec_fromAnticipated'' v AM M where

@[simp]
def newAnticipatedSRDetEvent_fromAnticipated'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : AnticipatedSRDetEventSpec_fromAnticipated'' v AM M) : AnticipatedRDetEvent v AM M Unit Unit :=
  newAnticipatedFRDetEvent_fromAnticipated ev.toAnticipatedFRDetEventSpec_fromAnticipated

structure ConvergentSRDetEventSpec (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M] (α) (β)
  extends ConvergentFRDetEventSpec v AM M α β where

@[simp]
def newConvergentSRDetEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : ConvergentSRDetEventSpec v AM M α β) : ConvergentRDetEvent v AM M α β :=
  newConvergentFRDetEvent ev.toConvergentFRDetEventSpec

structure ConvergentSRDetEventSpec' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M] (α)
  extends ConvergentFRDetEventSpec' v AM M α where

@[simp]
def newConvergentSRDetEvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : ConvergentSRDetEventSpec' v AM M α) : ConvergentRDetEvent v AM M α Unit :=
  newConvergentFRDetEvent ev.toConvergentFRDetEventSpec

structure ConvergentSRDetEventSpec'' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M]
  extends ConvergentFRDetEventSpec'' v AM M where

@[simp]
def newConvergentSRDetEvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : ConvergentSRDetEventSpec'' v AM M) : ConvergentRDetEvent v AM M Unit Unit :=
  newConvergentFRDetEvent ev.toConvergentFRDetEventSpec
