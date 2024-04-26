
import EventSystems.Refinement.Functional.NonDet.Basic
import EventSystems.Refinement.Relational.NonDet.Convergent

structure AnticipatedFRNDEventSpecFromOrdinary (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M] (α) (β)
  extends AnticipatedRNDEventSpecFromOrdinary v AM M α β where

@[simp]
def newAnticipatedFRNDEventSpecFromOrdinary [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AnticipatedFRNDEventSpecFromOrdinary v AM M α β) : AnticipatedRNDEvent v AM M α β :=
  newAnticipatedRNDEventfromOrdinary ev.toAnticipatedRNDEventSpecFromOrdinary

structure AnticipatedFRNDEventSpecFromOrdinary' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M] (α)
  extends AnticipatedRNDEventSpecFromOrdinary' v AM M α where

@[simp]
def newAnticipatedFRNDEventSpecFromOrdinary' [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AnticipatedFRNDEventSpecFromOrdinary' v AM M α) : AnticipatedRNDEvent v AM M α Unit :=
  newAnticipatedRNDEventfromOrdinary ev.toAnticipatedRNDEventSpecFromOrdinary

structure AnticipatedFRNDEventSpecFromOrdinary'' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M]
  extends AnticipatedRNDEventSpecFromOrdinary'' v AM M where

@[simp]
def newAnticipatedFRNDEventSpecFromOrdinary'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AnticipatedFRNDEventSpecFromOrdinary'' v AM M) : AnticipatedRNDEvent v AM M Unit Unit :=
  newAnticipatedRNDEventfromOrdinary ev.toAnticipatedRNDEventSpecFromOrdinary

structure AnticipatedFRNDEventSpecFromAnticipated (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M] (α) (β)
  extends AnticipatedRNDEventSpecFromAnticipated v AM M α β where

@[simp]
def newAnticipatedFRNDEventSpecFromAnticipated [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AnticipatedFRNDEventSpecFromAnticipated v AM M α β) : AnticipatedRNDEvent v AM M α β :=
  newAnticipatedRNDEventfromAnticipated ev.toAnticipatedRNDEventSpecFromAnticipated

structure AnticipatedFRNDEventSpecFromAnticipated' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M] (α)
  extends AnticipatedRNDEventSpecFromAnticipated' v AM M α where

@[simp]
def newAnticipatedFRNDEventSpecFromAnticipated' [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AnticipatedFRNDEventSpecFromAnticipated' v AM M α) : AnticipatedRNDEvent v AM M α Unit :=
  newAnticipatedRNDEventfromAnticipated ev.toAnticipatedRNDEventSpecFromAnticipated

structure AnticipatedFRNDEventSpecFromAnticipated'' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M]
  extends AnticipatedRNDEventSpecFromAnticipated'' v AM M where

@[simp]
def newAnticipatedFRNDEventSpecFromAnticipated'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AnticipatedFRNDEventSpecFromAnticipated'' v AM M) : AnticipatedRNDEvent v AM M Unit Unit :=
  newAnticipatedRNDEventfromAnticipated ev.toAnticipatedRNDEventSpecFromAnticipated

structure ConvergentFRNDEventSpec (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M] (α) (β)
  extends ConvergentRNDEventSpec v AM M α β where

@[simp]
def newConvergentFRNDEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : ConvergentFRNDEventSpec v AM M α β) : ConvergentRNDEvent v AM M α β :=
  newConvergentRNDEvent ev.toConvergentRNDEventSpec

structure ConvergentFRNDEventSpec' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M] (α)
  extends ConvergentRNDEventSpec' v AM M α where

@[simp]
def newConvergentFRNDEvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : ConvergentFRNDEventSpec' v AM M α) : ConvergentRNDEvent v AM M α Unit :=
  newConvergentRNDEvent ev.toConvergentRNDEventSpec

structure ConvergentFRNDEventSpec'' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M]
  extends ConvergentRNDEventSpec'' v AM M where

@[simp]
def newConvergentFRNDEvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : ConvergentFRNDEventSpec'' v AM M) : ConvergentRNDEvent v AM M Unit Unit :=
  newConvergentRNDEvent ev.toConvergentRNDEventSpec
