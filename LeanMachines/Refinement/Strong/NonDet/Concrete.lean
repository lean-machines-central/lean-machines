import LeanMachines.Refinement.Strong.NonDet.Basic
import LeanMachines.Refinement.Functional.NonDet.Concrete

open Refinement
open FRefinement
open SRefinement

@[simp]
def newConcreteSRNDEvent [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : ConcreteFRNDEventSpec AM M α β) : OrdinaryRNDEvent AM M α β :=
  newConcreteFRNDEvent ev

@[simp]
def newConcreteSRNDEvent' [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : ConcreteFRNDEventSpec' AM M α) : OrdinaryRNDEvent AM M α Unit :=
  newConcreteSRNDEvent ev.toConcreteFRNDEventSpec

@[simp]
def newConcreteSRNDEvent'' [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : ConcreteFRNDEventSpec'' AM M) : OrdinaryRNDEvent AM M Unit Unit :=
  newConcreteSRNDEvent ev.toConcreteFRNDEventSpec

/- Anticipated concrete events -/

@[simp]
def newConcreteAnticipatedSRNDEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : ConcreteAnticipatedFRNDEventSpec v AM M α β) : AnticipatedRNDEvent v AM M α β :=
  newConcreteAnticipatedFRNDEvent ev

@[simp]
def newConcreteAnticipatedSRNDEvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : ConcreteAnticipatedFRNDEventSpec' v AM M α) : AnticipatedRNDEvent v AM M α Unit :=
  newConcreteAnticipatedSRNDEvent ev.toConcreteAnticipatedFRNDEventSpec

@[simp]
def newConcreteAnticipatedSRNDEvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : ConcreteAnticipatedFRNDEventSpec'' v AM M) : AnticipatedRNDEvent v AM M Unit Unit :=
  newConcreteAnticipatedSRNDEvent ev.toConcreteAnticipatedFRNDEventSpec


/- Convergent concrete events -/

@[simp]
def newConcreteConvergentSRNDEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : ConcreteConvergentFRNDEventSpec v AM M α β) : ConvergentRNDEvent v AM M α β :=
  newConcreteConvergentFRNDEvent ev

@[simp]
def newConcreteConvergentSRNDEvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : ConcreteConvergentFRNDEventSpec' v AM M α) : ConvergentRNDEvent v AM M α Unit :=
  newConcreteConvergentSRNDEvent ev.toConcreteConvergentFRNDEventSpec

@[simp]
def newConcreteConvergentSRNDEvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : ConcreteConvergentFRNDEventSpec'' v AM M) : ConvergentRNDEvent v AM M Unit Unit :=
  newConcreteConvergentSRNDEvent ev.toConcreteConvergentFRNDEventSpec
