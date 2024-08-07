
import LeanMachines.Refinement.Strong.Basic
import LeanMachines.Refinement.Functional.Concrete

open Refinement
open FRefinement
open SRefinement

@[simp]
def newConcreteSREvent [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
   (ev : ConcreteFREventSpec AM M α β) : OrdinaryRDetEvent AM M α β :=
  newConcreteFREvent ev

@[simp]
def newConcreteSREvent' [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
   (ev : ConcreteFREventSpec' AM M α) : OrdinaryRDetEvent AM M α Unit :=
  newConcreteFREvent ev.toConcreteFREventSpec

@[simp]
def newConcreteSREvent'' [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
   (ev : ConcreteFREventSpec'' AM M) : OrdinaryRDetEvent AM M Unit Unit :=
  newConcreteFREvent ev.toConcreteFREventSpec

/- Anticipated concrete events -/

@[simp]
def newConcreteAnticipatedSREvent [Preorder v] [WellFoundedLT v]
                       [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
   (ev : ConcreteAnticipatedFREventSpec v AM M α β) : AnticipatedRDetEvent v AM M α β :=
  newConcreteAnticipatedFREvent ev

@[simp]
def newConcreteAnticipatedSREvent' [Preorder v] [WellFoundedLT v]
                       [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
   (ev : ConcreteAnticipatedFREventSpec' v AM M α) : AnticipatedRDetEvent v AM M α Unit :=
  newConcreteAnticipatedREvent ev.toConcreteAnticipatedREventSpec

@[simp]
def newConcreteAnticipatedSREvent'' [Preorder v] [WellFoundedLT v]
                       [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
   (ev : ConcreteAnticipatedFREventSpec'' v AM M) : AnticipatedRDetEvent v AM M Unit Unit :=
  newConcreteAnticipatedFREvent ev.toConcreteAnticipatedFREventSpec


/- Convergent concrete events -/

@[simp]
def newConcreteConvergentSREvent [Preorder v] [WellFoundedLT v]
                       [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
   (ev : ConcreteConvergentFREventSpec v AM M α β) : ConvergentRDetEvent v AM M α β :=
  newConcreteConvergentFREvent ev

@[simp]
def newConcreteConvergentSREvent' [Preorder v] [WellFoundedLT v]
                       [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
   (ev : ConcreteConvergentFREventSpec' v AM M α) : ConvergentRDetEvent v AM M α Unit :=
  newConcreteConvergentREvent ev.toConcreteConvergentREventSpec

@[simp]
def newConcreteConvergentSREvent'' [Preorder v] [WellFoundedLT v]
                       [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
   (ev : ConcreteConvergentFREventSpec'' v AM M) : ConvergentRDetEvent v AM M Unit Unit :=
  newConcreteConvergentFREvent ev.toConcreteConvergentFREventSpec
