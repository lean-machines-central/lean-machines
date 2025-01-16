
import LeanMachines.Refinement.Strong.Basic
import LeanMachines.Refinement.Relational.Convergent
import LeanMachines.Refinement.Functional.Convergent

@[simp]
def newAnticipatedSREventfromOrdinary [Preorder v] [@Machine ACTX AM] [@Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryEvent AM α' β')
  (ev : AnticipatedFREventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : AnticipatedREvent v AM M α β α' β' :=
  newAnticipatedFREventfromOrdinary abs ev

@[simp]
def newAnticipatedSREventfromOrdinary' [Preorder v] [@Machine ACTX AM] [@Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryEvent AM α' Unit)
  (ev : AnticipatedFREventSpec' v AM M (α:=α) (α':=α') abs) : AnticipatedREvent v AM M α Unit α' Unit :=
  newAnticipatedSREventfromOrdinary abs ev.toAnticipatedFREventSpec

@[simp]
def newAnticipatedSREventfromOrdinary'' [Preorder v] [@Machine ACTX AM] [@Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryEvent AM Unit Unit)
  (ev : AnticipatedFREventSpec'' v AM M abs) : AnticipatedREvent v AM M Unit Unit :=
  newAnticipatedSREventfromOrdinary abs ev.toAnticipatedFREventSpec

@[simp]
def newAnticipatedSREventfromAnticipated [Preorder v] [@Machine ACTX AM] [@Machine CTX M] [SRefinement AM M]
  (abs : AnticipatedEvent v AM α' β')
  (ev : AnticipatedFREventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs.toOrdinaryEvent) : AnticipatedREvent v AM M α β α' β' :=
  newAnticipatedFREventfromAnticipated abs ev

@[simp]
def newAnticipatedSREventfromAnticipated' [Preorder v] [@Machine ACTX AM] [@Machine CTX M] [SRefinement AM M]
  (abs : AnticipatedEvent v AM α' Unit)
  (ev : AnticipatedFREventSpec' v AM M (α:=α) (α':=α') abs.toOrdinaryEvent) : AnticipatedREvent v AM M α Unit α' Unit :=
  newAnticipatedSREventfromAnticipated abs ev.toAnticipatedFREventSpec

@[simp]
def newAnticipatedSREventfromAnticipated'' [Preorder v] [@Machine ACTX AM] [@Machine CTX M] [SRefinement AM M]
  (abs : AnticipatedEvent v AM Unit Unit)
  (ev : AnticipatedFREventSpec'' v AM M abs.toOrdinaryEvent) : AnticipatedREvent v AM M Unit Unit :=
  newAnticipatedSREventfromAnticipated abs ev.toAnticipatedFREventSpec

@[simp]
def newConvergentSREvent [Preorder v] [WellFoundedLT v] [@Machine ACTX AM] [@Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryEvent AM α' β') (ev : ConvergentFREventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : ConvergentREvent v AM M α β α' β' :=
  newConvergentFREvent abs ev

@[simp]
def newConvergentSREvent' [Preorder v] [WellFoundedLT v] [@Machine ACTX AM] [@Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryEvent AM α' Unit) (ev : ConvergentFREventSpec' v AM M (α:=α) (α':=α') abs) : ConvergentREvent v AM M α Unit α' Unit :=
  newConvergentSREvent abs ev.toConvergentFREventSpec

@[simp]
def newConvergentSREvent'' [Preorder v] [WellFoundedLT v] [@Machine ACTX AM] [@Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryEvent AM Unit Unit) (ev : ConvergentFREventSpec'' v AM M abs) : ConvergentREvent v AM M Unit Unit :=
  newConvergentSREvent abs ev.toConvergentFREventSpec
