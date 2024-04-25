
import EventSystems.Refinement.Functional.Basic

open Refinement
open FRefinement

class SRefinement {ACTX : outParam (Type u₁)} (AM)
                 {CTX : outParam (Type u₂)} (M)
                 [Machine ACTX AM] [Machine CTX M] extends FRefinement AM M where

  unlift (m : M) (am' : AM): M

  lift_unlift (m : M) (am' : AM):
    Machine.invariant m → Machine.invariant am'
    → lift (unlift m am') = am'

structure SREventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M] (α) (β)
  extends FREventSpec AM M α β where

@[simp]
def newSREvent [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : SREventSpec AM M α β) : OrdinaryREvent AM M α β :=
  newFREvent ev.toFREventSpec

structure SREventSpec' (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M] (α)
  extends FREventSpec' AM M α where

@[simp]
def newSREvent' [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : SREventSpec' AM M α) : OrdinaryREvent AM M α Unit :=
  newFREvent ev.toFREventSpec

structure SREventSpec'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M]
  extends FREventSpec'' AM M where

@[simp]
def newSREvent'' [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : SREventSpec'' AM M) : OrdinaryREvent AM M Unit Unit :=
  newFREvent ev.toFREventSpec

/- Initialization events -/

structure InitSREventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M] (α) (β)
  extends InitFREventSpec AM M α β where

@[simp]
def newInitSREvent [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : InitSREventSpec AM M α β) : InitREvent AM M α β :=
  newInitFREvent ev.toInitFREventSpec

structure InitSREventSpec' (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M] (α)
  extends InitFREventSpec' AM M α where

@[simp]
def newInitSREvent' [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : InitSREventSpec' AM M α) : InitREvent AM M α Unit :=
  newInitFREvent ev.toInitFREventSpec

structure InitSREventSpec'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M]
  extends InitFREventSpec'' AM M where

@[simp]
def newInitSREvent'' [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : InitSREventSpec'' AM M) : InitREvent AM M Unit Unit :=
  newInitFREvent ev.toInitFREventSpec
