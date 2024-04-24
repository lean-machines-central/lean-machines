
import EventSystems.Refinement.Relational.Basic

class FRefinement {ACTX : outParam (Type u₁)} (AM)
                  {CTX : outParam (Type u₂)} (M)
                  [Machine ACTX AM] [Machine CTX M] extends Refinement AM M where

  lift (m : M): AM

  lift_ref (m : M):
    Machine.invariant m
    → refine (lift m) m

  refine_uniq (am am' : AM) (m : M):
    Machine.invariant m
    → refine am m → refine am' m
    → am = am'

open Refinement
open FRefinement

theorem lift_safe [Machine ACTX AM] [Machine CTX M] [instR:FRefinement AM M] (m : M):
  Machine.invariant m
  → Machine.invariant (M:=AM) (lift m) :=
by
  intro Hinv₁
  have Href := FRefinement.lift_ref (self:=instR) m Hinv₁
  apply refine_safe (M:=M) (lift m) m Hinv₁ Href

@[simp]
def defaultRefine {AM} [Machine ACTX AM] {M} [Machine CTX M]
  (abs : M → AM) (m : M) (am : AM) :=
  am = abs m

theorem defaultRefine_safe {AM} [Machine ACTX AM] {M} [Machine CTX M]
  (abs : M → AM) (m : M) (am : AM) (Habs: Machine.invariant m → Machine.invariant (abs m)):
    Machine.invariant m
    → defaultRefine abs m am
    → Machine.invariant am :=
by
  intros Hinv Href
  unfold defaultRefine at Href
  rw [Href]
  apply Habs
  assumption

theorem defaultRefine_ref {AM} [Machine ACTX AM] {M} [Machine CTX M]
  (abs : M → AM) (m : M) (am am' : AM):
  Machine.invariant m
    → defaultRefine abs m am → defaultRefine abs m am'
    → am = am' :=
by
  simp
  intros _ Href₁ Href₂
  simp [*]

structure FREventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M] (α) (β)
  extends EventSpec M α β where

  abstract : OrdinaryEvent AM α β

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → abstract.guard (lift m) x

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let (y, m') := action m x
      let (z, am') := abstract.action (lift m) x
      y = z ∧ am' = (lift m')

@[simp]
def newFREvent [Machine ACTX AM] [Machine CTX M] [instFR:FRefinement AM M] (ev : FREventSpec AM M α β) : OrdinaryREvent AM M α β :=
  {
    to_Event := ev.toEventSpec.to_Event
    po := {
      safety := ev.safety
      abstract := ev.abstract.to_Event
      strengthening := fun m x => by simp
                                     intros Hinv Hgrd am Href
                                     have Href' := lift_ref (self:=instFR) m Hinv
                                     have Huniq := refine_uniq (self:=instFR) am (lift m) m Hinv Href Href'
                                     rw [Huniq]
                                     apply ev.strengthening <;> assumption

      simulation := fun m x => by simp
                                  intros Hinv Hgrd am Href
                                  have Href' := lift_ref (self:=instFR) m Hinv
                                  have Huniq := refine_uniq (self:=instFR) am (lift m) m Hinv Href Href'
                                  rw [Huniq]
                                  obtain ⟨Hsim₁, Hsim₂⟩ := ev.simulation m x Hinv Hgrd
                                  simp [Hsim₁]
                                  rw [Hsim₂]
                                  apply lift_ref
                                  apply ev.safety <;> assumption
    }
  }

structure FREventSpec' (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M] (α)
  extends EventSpec' M α where

  abstract : OrdinaryEvent AM α Unit

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → abstract.guard (lift m) x

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := action m x
      let ((), am') := abstract.action (lift m) x
      y = z ∧ am' = (lift m')

@[simp]
def FREventSpec'.toFREventSpec [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : FREventSpec' AM M α) : FREventSpec AM M α Unit :=
  {
    toEventSpec := ev.toEventSpec
    abstract := ev.abstract
    strengthening := ev.strengthening
    simulation := fun m x => by apply ev.simulation
  }

@[simp]
def newFREvent' [Machine ACTX AM] [Machine CTX M] [instFR:FRefinement AM M] (ev : FREventSpec' AM M α) : OrdinaryREvent AM M α Unit :=
  newFREvent ev.toFREventSpec

structure FREventSpec'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M]
  extends EventSpec'' M where

  abstract : OrdinaryEvent AM Unit Unit

  strengthening (m : M):
    Machine.invariant m
    → guard m
    → abstract.guard (lift m) ()

  simulation (m : M):
    Machine.invariant m
    → guard m
    → let m' := action m
      let ((), am') := abstract.action (lift m) ()
      y = z ∧ am' = (lift m')

@[simp]
def FREventSpec''.toFREventSpec [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : FREventSpec'' AM M) : FREventSpec AM M Unit Unit :=
  {
    toEventSpec := ev.toEventSpec
    abstract := ev.abstract
    strengthening := fun m _ => by apply ev.strengthening
    simulation := fun m _ => by apply ev.simulation
  }

@[simp]
def newFREvent'' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M] (ev : FREventSpec'' AM M) : OrdinaryREvent AM M Unit Unit :=
  newFREvent ev.toFREventSpec

structure InitFREventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M] (α) (β)
  extends InitEventSpec M α β where

  abstract : InitEvent AM α β

  strengthening (x : α):
    guard x
    → abstract.guard Machine.reset x

  simulation (x : α):
    guard x
    → let (y, m') := init x
      let (z, am') := abstract.action Machine.reset x
      y = z ∧ am' = lift m'

@[simp]
def InitFREventSpec.toInitREventSpec [Machine ACTX AM] [Machine CTX M] [FRefinement AM M] (ev : InitFREventSpec AM M α β) : InitREventSpec AM M α β :=
  {
    toInitEventSpec := ev.toInitEventSpec
    abstract := ev.abstract
    strengthening := ev.strengthening
    simulation := fun x => by simp
                              intro Hgrd
                              have Hsim := ev.simulation x Hgrd
                              simp at Hsim
                              simp [Hsim]
                              apply lift_ref
                              apply ev.safety ; assumption
  }

@[simp]
def newInitFREvent [Machine ACTX AM] [Machine CTX M] [FRefinement AM M] (ev : InitFREventSpec AM M α β) : InitREvent AM M α β :=
  newInitREvent ev.toInitREventSpec

structure InitFREventSpec' (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M] (α)
  extends InitEventSpec' M α where

  abstract : InitEvent AM α Unit

  strengthening (x : α):
    guard x
    → abstract.guard Machine.reset x

  simulation (x : α):
    guard x
    → let m' := init x
      let ((), am') := abstract.action Machine.reset x
      am' = lift m'

@[simp]
def InitFREventSpec'.toInitFREventSpec  [Machine ACTX AM] [Machine CTX M] [FRefinement AM M] (ev : InitFREventSpec' AM M α) : InitFREventSpec AM M α Unit :=
  {
    toInitEventSpec := ev.toInitEventSpec
    abstract := ev.abstract
    simulation := fun x => by simp
                              intro Hgrd
                              apply ev.simulation ; assumption
    strengthening := fun x => by apply ev.strengthening
  }

@[simp]
def newInitFREvent' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M] (ev : InitFREventSpec' AM M α) : InitREvent AM M α Unit :=
  newInitFREvent (ev.toInitFREventSpec)

structure InitFREventSpec'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M]
  extends InitEventSpec'' M where

  abstract : InitEvent AM Unit Unit

  strengthening:
    guard → abstract.guard Machine.reset ()

  simulation:
    guard
    → let m' := init
      let ((), am') := abstract.action Machine.reset ()
      am' = lift m'

@[simp]
def InitFREventSpec''.toInitFREventSpec  [Machine ACTX AM] [Machine CTX M] [FRefinement AM M] (ev : InitFREventSpec'' AM M) : InitFREventSpec AM M Unit Unit :=
  {
    toInitEventSpec := ev.toInitEventSpec
    abstract := ev.abstract
    simulation := fun () => by simp
                               apply ev.simulation
    strengthening := fun () => by simp
                                  intro Hgrd
                                  apply ev.strengthening ; assumption
  }

@[simp]
def newInitFREvent'' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M] (ev : InitFREventSpec'' AM M) : InitREvent AM M Unit Unit :=
  newInitFREvent (ev.toInitFREventSpec)
