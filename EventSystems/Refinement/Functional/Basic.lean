
import EventSystems.Event.Basic
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
  (abs : M → AM) (am : AM) (m : M) :=
  am = abs m

theorem defaultRefine_safe {AM} [Machine ACTX AM] {M} [Machine CTX M]
  (abs : M → AM)  (am : AM) (m : M) (Habs: Machine.invariant m → Machine.invariant (abs m)):
    Machine.invariant m
    → defaultRefine abs am m
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
    → defaultRefine abs am m → defaultRefine abs am' m
    → am = am' :=
by
  simp
  intros _ Href₁ Href₂
  simp [*]

structure FREventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [instfr: FRefinement AM M]
  {α β α' β'} (abstract : OrdinaryEvent AM α' β')
  extends EventSpec M α β where

  lift_in : α → α'
  lift_out : β → β'

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → abstract.guard (lift m) (lift_in x)

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let (y, m') := action m x
      let (z, am') := abstract.action (lift m) (lift_in x)
      lift_out y = z ∧ am' = (lift m')


@[simp]
def FREventSpec.toREventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  {α β α' β'} (abs : OrdinaryEvent AM α' β')
  (ev : FREventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : REventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs :=
  {
    toEventSpec := ev.toEventSpec

    lift_in := ev.lift_in
    lift_out := ev.lift_out

    strengthening := fun m x => by
      intros Hinv Hgrd am Href
      have Hst := ev.strengthening m x Hinv Hgrd
      have Href' := lift_ref (self:=instFR) m Hinv
      have Huniq := refine_uniq (self:=instFR) am (lift m) m Hinv Href Href'
      rw [Huniq]
      exact Hst

    simulation := fun m x => by
      simp
      intros Hinv Hgrd am Href
      have Hsim := ev.simulation m x Hinv Hgrd
      simp at Hsim
      obtain ⟨Hsim₁, Hsim₂⟩ := Hsim
      have Href' := lift_ref (self:=instFR) m Hinv
      have Huniq := refine_uniq (self:=instFR) am (lift m) m Hinv Href Href'
      rw [Huniq]
      simp [Hsim₁]
      rw [Hsim₂]
      apply lift_ref
      · apply ev.safety m x Hinv Hgrd
  }

@[simp]
def newFREvent [Machine ACTX AM] [Machine CTX M] [instFR:FRefinement AM M]
  (abs : OrdinaryEvent AM α' β') (ev : FREventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : OrdinaryREvent AM M α β α' β' :=
  newREvent abs ev.toREventSpec

structure FREventSpec' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instfr: FRefinement AM M]
  {α α'} (abstract : OrdinaryEvent AM α' Unit)
  extends EventSpec' M α where

  lift_in : α → α'

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → abstract.guard (lift m) (lift_in x)

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := action m x
      let ((), am') := abstract.action (lift m) (lift_in x)
      am' = (lift m')

@[simp]
def FREventSpec'.toFREventSpec [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  {α α'} (abs : OrdinaryEvent AM α' Unit)
  (ev : FREventSpec' AM M (α:=α) (α':=α') abs) : FREventSpec AM M (α:=α) (β:=Unit) (α':=α') (β':=Unit) abs :=
  {
    toEventSpec := ev.toEventSpec
    lift_in := ev.lift_in
    lift_out := id
    strengthening := ev.strengthening
    simulation := fun m x => by simp ; apply ev.simulation
  }

@[simp]
def newFREvent' [Machine ACTX AM] [Machine CTX M] [instFR:FRefinement AM M]
  (abs : OrdinaryEvent AM α' Unit) (ev : FREventSpec' AM M (α:=α) (α':=α') abs) : OrdinaryREvent AM M α Unit α' Unit :=
  newFREvent abs ev.toFREventSpec

structure FREventSpec'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instfr: FRefinement AM M]
  (abstract : OrdinaryEvent AM Unit Unit)
  extends EventSpec'' M where

  strengthening (m : M):
    Machine.invariant m
    → guard m
    → abstract.guard (lift m) ()

  simulation (m : M):
    Machine.invariant m
    → guard m
    → let m' := action m
      let ((), am') := abstract.action (lift m) ()
      am' = (lift m')

@[simp]
def FREventSpec''.toFREventSpec [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM Unit Unit)
  (ev : FREventSpec'' AM M abs) : FREventSpec AM M (α:=Unit) (β:=Unit) (α':=Unit) (β':=Unit) abs :=
  {
    toEventSpec := ev.toEventSpec
    lift_in := id
    lift_out := id
    strengthening := fun m () => ev.strengthening m
    simulation := fun m () => by
      simp
      intros Hinv Hgrd
      apply ev.simulation <;> assumption
  }

@[simp]
def newFREvent'' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM Unit Unit) (ev : FREventSpec'' AM M abs) : OrdinaryREvent AM M Unit Unit :=
  newFREvent abs ev.toFREventSpec


/- Initialization events -/

structure InitFREventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [instFR: FRefinement AM M]
  {α β α' β'} (abstract : InitEvent AM α' β')
  extends InitEventSpec M α β where

  lift_in : α → α'
  lift_out : β → β'

  strengthening (x : α):
    guard x
    → abstract.guard (lift_in x)

  simulation (x : α):
    guard x
    → let (y, m') := init x
      let (z, am') := abstract.init (lift_in x)
      lift_out y = z ∧ am' = lift m'

@[simp]
def InitFREventSpec.toInitREventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  {abs : InitEvent AM α' β'}
  (ev : InitFREventSpec (instFR:=instFR) (α:=α) (β:=β) (α':=α') (β':=β') abs) : InitREventSpec (instR:=instFR.toRefinement) (α:=α) (β:=β) (α':=α') (β':=β') abs :=
  {
    toInitEventSpec := ev.toInitEventSpec
    lift_in := ev.lift_in
    lift_out := ev.lift_out
    strengthening := ev.strengthening
    simulation := fun x => by
      simp
      intro Hgrd
      have Hsim := ev.simulation x Hgrd
      simp at Hsim
      simp [Hsim]
      apply lift_ref
      apply ev.safety
      assumption
  }

@[simp]
def newInitFREvent [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : InitEvent AM α' β') (ev : InitFREventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : InitREvent AM M α β α' β' :=
  newInitREvent abs ev.toInitREventSpec

structure InitFREventSpec' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instFR: FRefinement AM M]
  {α α'} (abstract : InitEvent AM α' Unit)
  extends InitEventSpec' M α where

  lift_in : α → α'

  strengthening (x : α):
    guard x
    → abstract.guard (lift_in x)

  simulation (x : α):
    guard x
    → let m' := init x
      let ((), am') := abstract.init (lift_in x)
      am' = lift m'

@[simp]
def InitFREventSpec'.toInitFREventSpec [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  {α α'} (abs : InitEvent AM α' Unit)
  (ev : InitFREventSpec' AM M (α:=α) (α':=α') abs) : InitFREventSpec AM M (α:=α) (β:=Unit) (α':=α') (β':=Unit) abs :=
  {
    toInitEventSpec := ev.toInitEventSpec
    lift_in := ev.lift_in
    lift_out := id
    strengthening := ev.strengthening
    simulation := fun x => by
      simp
      intros Hgrd
      apply ev.simulation ; assumption
  }

@[simp]
def newInitFREvent' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : InitEvent AM α' Unit) (ev : InitFREventSpec' AM M (α:=α) (α':=α') abs) : InitREvent AM M α Unit α' Unit :=
  newInitFREvent abs ev.toInitFREventSpec

structure InitFREventSpec'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instFR: FRefinement AM M]
  (abstract : InitEvent AM Unit Unit)
  extends InitEventSpec'' M where

  strengthening:
    guard
    → abstract.guard ()

  simulation:
    guard
    → let m' := init
      let ((), am') := abstract.init ()
      am' = lift m'

@[simp]
def InitFREventSpec''.toInitFREventSpec [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : InitEvent AM Unit Unit)
  (ev : InitFREventSpec'' AM M abs) : InitFREventSpec AM M (α:=Unit) (β:=Unit) (α':=Unit) (β':=Unit) abs :=
  {
    toInitEventSpec := ev.toInitEventSpec
    lift_in := id
    lift_out := id
    strengthening := fun () => ev.strengthening
    simulation := fun () => by
      simp
      intros Hgrd
      apply ev.simulation ; assumption
  }

@[simp]
def newInitFREvent'' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : InitEvent AM Unit Unit) (ev : InitFREventSpec'' AM M abs) : InitREvent AM M Unit Unit :=
  newInitFREvent abs ev.toInitFREventSpec
