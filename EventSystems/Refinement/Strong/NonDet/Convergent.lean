import EventSystems.Refinement.Strong.Basic
import EventSystems.Refinement.Functional.NonDet.Convergent
import EventSystems.Event.Convergent

open Refinement
open FRefinement
open SRefinement

structure AnticipatedSRNDEventSpecFromOrdinary (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M] (α) (β)
  extends AnticipatedFRNDEventSpecFromOrdinary v AM M α β where

@[simp]
def newAnticipatedSRNDEventFromOrdinary [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : AnticipatedSRNDEventSpecFromOrdinary v AM M α β) : AnticipatedRNDEvent v AM M α β :=
  newAnticipatedFRNDEventFromOrdinary ev.toAnticipatedFRNDEventSpecFromOrdinary

structure AnticipatedSRNDEventSpecFromOrdinary' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M] (α)
  extends AnticipatedFRNDEventSpecFromOrdinary' v AM M α where

@[simp]
def newAnticipatedSRNDEventFromOrdinary' [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : AnticipatedSRNDEventSpecFromOrdinary' v AM M α) : AnticipatedRNDEvent v AM M α Unit :=
  newAnticipatedFRNDEventFromOrdinary ev.toAnticipatedFRNDEventSpecFromOrdinary

structure AnticipatedSRNDEventSpecFromOrdinary'' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M]
  extends AnticipatedFRNDEventSpecFromOrdinary'' v AM M where

@[simp]
def newAnticipatedSRNDEventFromOrdinary'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : AnticipatedSRNDEventSpecFromOrdinary'' v AM M) : AnticipatedRNDEvent v AM M Unit Unit :=
  newAnticipatedFRNDEventFromOrdinary ev.toAnticipatedFRNDEventSpecFromOrdinary

structure AnticipatedSRNDEventSpecFromAnticipated (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M] (α) (β)
  extends AnticipatedFRNDEventSpecFromAnticipated v AM M α β where

@[simp]
def newAnticipatedSRNDEventFromAnticipated [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : AnticipatedSRNDEventSpecFromAnticipated v AM M α β) : AnticipatedRNDEvent v AM M α β :=
  newAnticipatedFRNDEventFromAnticipated ev.toAnticipatedFRNDEventSpecFromAnticipated

structure AnticipatedSRNDEventSpecFromAnticipated' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M] (α)
  extends AnticipatedFRNDEventSpecFromAnticipated' v AM M α where

@[simp]
def newAnticipatedSRNDEventFromAnticipated' [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : AnticipatedSRNDEventSpecFromAnticipated' v AM M α) : AnticipatedRNDEvent v AM M α Unit :=
  newAnticipatedFRNDEventFromAnticipated ev.toAnticipatedFRNDEventSpecFromAnticipated

structure AnticipatedSRNDEventSpecFromAnticipated'' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M]
  extends AnticipatedFRNDEventSpecFromAnticipated'' v AM M where

@[simp]
def newAnticipatedSRNDEventFromAnticipated'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : AnticipatedSRNDEventSpecFromAnticipated'' v AM M) : AnticipatedRNDEvent v AM M Unit Unit :=
  newAnticipatedFRNDEventFromAnticipated ev.toAnticipatedFRNDEventSpecFromAnticipated

structure ConvergentSRNDEventSpec (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M] (α) (β)
  extends ConvergentFRNDEventSpec v AM M α β where

@[simp]
def newConvergentSRNDEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : ConvergentSRNDEventSpec v AM M α β) : ConvergentRNDEvent v AM M α β :=
  newConvergentFRNDEvent ev.toConvergentFRNDEventSpec

structure ConvergentSRNDEventSpec' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M] (α)
  extends ConvergentFRNDEventSpec' v AM M α where

@[simp]
def newConvergentSRNDEvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : ConvergentSRNDEventSpec' v AM M α) : ConvergentRNDEvent v AM M α Unit :=
  newConvergentFRNDEvent ev.toConvergentFRNDEventSpec

structure ConvergentSRNDEventSpec'' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M]
  extends ConvergentFRNDEventSpec'' v AM M where

@[simp]
def newConvergentSRNDEvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : ConvergentSRNDEventSpec'' v AM M) : ConvergentRNDEvent v AM M Unit Unit :=
  newConvergentFRNDEvent ev.toConvergentFRNDEventSpec
