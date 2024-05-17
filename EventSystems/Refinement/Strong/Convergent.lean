
import EventSystems.Refinement.Strong.Basic
import EventSystems.Refinement.Relational.Convergent
import EventSystems.Refinement.Functional.Convergent

@[simp]
def newAnticipatedSREventfromOrdinary [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryEvent AM α' β')
  (ev : AnticipatedREventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : AnticipatedREvent v AM M α β α' β' :=
  newAnticipatedREventfromOrdinary abs ev

@[simp]
def newAnticipatedSREventfromOrdinary' [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryEvent AM α' Unit)
  (ev : AnticipatedREventSpec' v AM M (α:=α) (α':=α') abs) : AnticipatedREvent v AM M α Unit α' Unit :=
  newAnticipatedSREventfromOrdinary abs ev.toAnticipatedREventSpec

@[simp]
def newAnticipatedSREventfromOrdinary'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryEvent AM Unit Unit)
  (ev : AnticipatedREventSpec'' v AM M abs) : AnticipatedREvent v AM M Unit Unit :=
  newAnticipatedSREventfromOrdinary abs ev.toAnticipatedREventSpec

@[simp]
def newAnticipatedSREventfromAnticipated [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : AnticipatedEvent v AM α' β')
  (ev : AnticipatedREventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs.toOrdinaryEvent) : AnticipatedREvent v AM M α β α' β' :=
  newAnticipatedREventfromAnticipated abs ev

@[simp]
def newAnticipatedSREventfromAnticipated' [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : AnticipatedEvent v AM α' Unit)
  (ev : AnticipatedREventSpec' v AM M (α:=α) (α':=α') abs.toOrdinaryEvent) : AnticipatedREvent v AM M α Unit α' Unit :=
  newAnticipatedSREventfromAnticipated abs ev.toAnticipatedREventSpec

@[simp]
def newAnticipatedSREventfromAnticipated'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : AnticipatedEvent v AM Unit Unit)
  (ev : AnticipatedREventSpec'' v AM M abs.toOrdinaryEvent) : AnticipatedREvent v AM M Unit Unit :=
  newAnticipatedSREventfromAnticipated abs ev.toAnticipatedREventSpec

@[simp]
def newConvergentSREvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryEvent AM α' β') (ev : ConvergentREventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : ConvergentREvent v AM M α β α' β' :=
  newConvergentREvent abs ev

@[simp]
def newConvergentSREvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryEvent AM α' Unit) (ev : ConvergentREventSpec' v AM M (α:=α) (α':=α') abs) : ConvergentREvent v AM M α Unit α' Unit :=
  newConvergentSREvent abs ev.toConvergentREventSpec

@[simp]
def newConvergentSREvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryEvent AM Unit Unit) (ev : ConvergentREventSpec'' v AM M abs) : ConvergentREvent v AM M Unit Unit :=
  newConvergentSREvent abs ev.toConvergentREventSpec
