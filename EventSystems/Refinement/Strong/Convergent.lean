
import EventSystems.Refinement.Strong.Basic
import EventSystems.Refinement.Functional.Convergent

structure AnticipatedSREventSpecFromOrdinary (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M] (α) (β)
  extends AnticipatedFREventSpecFromOrdinary v AM M α β where

@[simp]
def newAnticipatedSREventfromOrdinary [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : AnticipatedSREventSpecFromOrdinary v AM M α β) : AnticipatedREvent v AM M α β :=
  newAnticipatedFREventfromOrdinary ev.toAnticipatedFREventSpecFromOrdinary

structure AnticipatedSREventSpecFromOrdinary' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M] (α)
  extends AnticipatedFREventSpecFromOrdinary' v AM M α where

@[simp]
def newAnticipatedSREventfromOrdinary' [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : AnticipatedSREventSpecFromOrdinary' v AM M α) : AnticipatedREvent v AM M α Unit :=
  newAnticipatedFREventfromOrdinary ev.toAnticipatedFREventSpecFromOrdinary

structure AnticipatedSREventSpecFromOrdinary'' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M]
  extends AnticipatedFREventSpecFromOrdinary'' v AM M where

@[simp]
def newAnticipatedSREventfromOrdinary'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : AnticipatedSREventSpecFromOrdinary'' v AM M) : AnticipatedREvent v AM M Unit Unit :=
  newAnticipatedFREventfromOrdinary ev.toAnticipatedFREventSpecFromOrdinary

structure AnticipatedSREventSpecFromAnticipated (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M] (α) (β)
  extends AnticipatedFREventSpecFromAnticipated v AM M α β where

@[simp]
def newAnticipatedSREventfromAnticipated [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : AnticipatedSREventSpecFromAnticipated v AM M α β) : AnticipatedREvent v AM M α β :=
  newAnticipatedFREventfromAnticipated ev.toAnticipatedFREventSpecFromAnticipated

structure AnticipatedSREventSpecFromAnticipated' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M] (α)
  extends AnticipatedFREventSpecFromAnticipated' v AM M α where

@[simp]
def newAnticipatedSREventfromAnticipated' [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : AnticipatedSREventSpecFromAnticipated' v AM M α) : AnticipatedREvent v AM M α Unit :=
  newAnticipatedFREventfromAnticipated ev.toAnticipatedFREventSpecFromAnticipated

structure AnticipatedSREventSpecFromAnticipated'' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M]
  extends AnticipatedFREventSpecFromAnticipated'' v AM M where

@[simp]
def newAnticipatedSREventfromAnticipated'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : AnticipatedSREventSpecFromAnticipated'' v AM M) : AnticipatedREvent v AM M Unit Unit :=
  newAnticipatedFREventfromAnticipated ev.toAnticipatedFREventSpecFromAnticipated

structure ConvergentSREventSpec (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M] (α) (β)
  extends ConvergentFREventSpec v AM M α β where

@[simp]
def newConvergentSREvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : ConvergentSREventSpec v AM M α β) : ConvergentREvent v AM M α β :=
  newConvergentFREvent ev.toConvergentFREventSpec

structure ConvergentSREventSpec' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M] (α)
  extends ConvergentFREventSpec' v AM M α where

@[simp]
def newConvergentSREvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : ConvergentSREventSpec' v AM M α) : ConvergentREvent v AM M α Unit :=
  newConvergentFREvent ev.toConvergentFREventSpec

structure ConvergentSREventSpec'' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M]
  extends ConvergentFREventSpec'' v AM M where

@[simp]
def newConvergentSREvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : ConvergentSREventSpec'' v AM M) : ConvergentREvent v AM M Unit Unit :=
  newConvergentFREvent ev.toConvergentFREventSpec
