
import EventSystems.Refinement.Functional.Basic
import EventSystems.Refinement.Relational.Convergent
import EventSystems.Event.Convergent

open Refinement
open FRefinement

@[simp]
def newAnticipatedFREventfromOrdinary [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM α' β') (ev : AnticipatedREventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : AnticipatedREvent v AM M α β α' β' :=
  newAnticipatedREventfromOrdinary abs ev

@[simp]
def newAnticipatedFREventfromOrdinary' [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM α' Unit) (ev : AnticipatedREventSpec' v AM M (α:=α) (α':=α') abs) : AnticipatedREvent v AM M α Unit α' Unit :=
  newAnticipatedREventfromOrdinary' abs ev

@[simp]
def newAnticipatedFREventfromOrdinary'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM Unit Unit) (ev : AnticipatedREventSpec'' v AM M abs) : AnticipatedREvent v AM M Unit Unit :=
  newAnticipatedREventfromOrdinary'' abs ev

@[simp]
def newAnticipatedFREventfromAnticipated [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : AnticipatedEvent v AM α' β') (ev : AnticipatedREventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs.toOrdinaryEvent) : AnticipatedREvent v AM M α β α' β' :=
  newAnticipatedREventfromAnticipated abs ev

@[simp]
def newAnticipatedFREventfromAnticipated' [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : AnticipatedEvent v AM α' Unit) (ev : AnticipatedREventSpec' v AM M (α:=α) (α':=α') abs.toOrdinaryEvent) : AnticipatedREvent v AM M α Unit α' Unit :=
  newAnticipatedREventfromAnticipated' abs ev

@[simp]
def newAnticipatedFREventfromAnticipated'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : AnticipatedEvent v AM Unit Unit) (ev : AnticipatedREventSpec'' v AM M abs.toOrdinaryEvent) : AnticipatedREvent v AM M Unit Unit :=
  newAnticipatedREventfromAnticipated'' abs ev

@[simp]
def newConvergentFREvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM α' β') (ev : ConvergentREventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : ConvergentREvent v AM M α β α' β' :=
  newConvergentREvent abs ev

@[simp]
def newConvergentFREvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM α' Unit) (ev : ConvergentREventSpec' v AM M (α:=α) (α':=α') abs) : ConvergentREvent v AM M α Unit α' Unit :=
  newConvergentREvent' abs ev

@[simp]
def newConvergentFREvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM Unit Unit) (ev : ConvergentREventSpec'' v AM M abs) : ConvergentREvent v AM M Unit Unit :=
  newConvergentREvent'' abs ev
