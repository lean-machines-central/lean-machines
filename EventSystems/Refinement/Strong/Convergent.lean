
import EventSystems.Refinement.Strong.Basic
import EventSystems.Refinement.Relational.Convergent
import EventSystems.Refinement.Functional.Convergent

@[simp]
def newAnticipatedSREventfromOrdinary [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryEvent AM α' β')
  (ev : AnticipatedREventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs.to_Event) : AnticipatedREvent v AM M α β α' β' :=
  newAnticipatedREventfromOrdinary abs ev

@[simp]
def newAnticipatedSREventfromAnticipated [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : AnticipatedEvent v AM α' β')
  (ev : AnticipatedREventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs.to_Event) : AnticipatedREvent v AM M α β α' β' :=
  newAnticipatedREventfromAnticipated abs ev

@[simp]
def newConvergentSREvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : _Event AM α' β') (ev : ConvergentREventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : ConvergentREvent v AM M α β α' β' :=
  newConvergentREvent abs ev
