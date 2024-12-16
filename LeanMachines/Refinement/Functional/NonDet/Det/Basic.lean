
import LeanMachines.Refinement.Functional.Basic
import LeanMachines.NonDet.Ordinary
import LeanMachines.Refinement.Relational.NonDet.Det.Basic

open Refinement
open FRefinement

structure FRDetEventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M]
  {α β α' β'} (abstract : OrdinaryNDEvent AM α' β')
  extends EventSpec M α β where

  lift_in : α → α'
  lift_out : β → β'

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → abstract.guard (lift m) (lift_in x)

  simulation (m : M) (x : α):
    (Hinv : Machine.invariant m)
    → (Hgrd : guard m x)
    → let (y, m') := action m x Hgrd
      abstract.effect (lift m) (lift_in x)
        (strengthening m x Hinv Hgrd)
        (lift_out y, lift m')

@[simp]
def FRDetEventSpec.toRDetEventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (abstract : OrdinaryNDEvent AM α' β') (ev : FRDetEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abstract) : RDetEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abstract :=
  {
    toEventSpec := ev.toEventSpec
    lift_in := ev.lift_in
    lift_out := ev.lift_out

    strengthening := fun m x => by
      intros Hinv Hgrd am Href
      have Hst := ev.strengthening m x Hinv Hgrd
      simp [refine] at Href
      simp [Href, Hst]

    simulation := fun m x => by
      simp
      intros Hinv Hgrd am Href
      have Hsim := ev.simulation m x Hinv Hgrd
      simp at Hsim
      exists (lift (ev.action m x Hgrd).2)
      simp [refine] at Href
      simp [Href, Hsim, refine]
  }

@[simp]
def newFRDetEvent [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryNDEvent AM α' β')
  (ev : FRDetEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : OrdinaryRDetEvent AM M α β α' β':=
  newRDetEvent abs ev.toRDetEventSpec

structure FRDetEventSpec' (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M]
  {α α'} (abstract : OrdinaryNDEvent AM α' Unit)
  extends EventSpec' M α where

  lift_in : α → α'

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → abstract.guard (lift m) (lift_in x)

  simulation (m : M) (x : α):
    (Hinv : Machine.invariant m)
    → (Hgrd : guard m x)
    → let m' := action m x Hgrd
      abstract.effect (lift m) (lift_in x)
        (strengthening m x Hinv Hgrd)
        ((), lift m')

@[simp]
def FRDetEventSpec'.toFRDetEventSpec [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abstract : OrdinaryNDEvent AM α' Unit) (ev : FRDetEventSpec' AM M (α:=α) (α':=α') abstract) : FRDetEventSpec AM M (α:=α) (β:=Unit) (α':=α') (β':=Unit) abstract :=
  {
    toEventSpec := ev.toEventSpec
    lift_in := ev.lift_in
    lift_out := id
    strengthening := ev.strengthening
    simulation := ev.simulation
  }

@[simp]
def newFRDetEvent' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryNDEvent AM α' Unit)
  (ev : FRDetEventSpec' AM M (α:=α) (α':=α') abs) : OrdinaryRDetEvent AM M α Unit α' Unit:=
  newFRDetEvent abs ev.toFRDetEventSpec

structure FRDetEventSpec'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M]
  (abstract : OrdinaryNDEvent AM Unit Unit)
  extends EventSpec'' M where

  strengthening (m : M):
    Machine.invariant m
    → guard m
    → abstract.guard (lift m) ()

  simulation (m : M):
    (Hinv : Machine.invariant m)
    → (Hgrd : guard m)
    → let m' := action m Hgrd
      abstract.effect (lift m) () (strengthening m Hinv Hgrd) ((), lift m')

@[simp]
def FRDetEventSpec''.toFRDetEventSpec [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abstract : OrdinaryNDEvent AM Unit Unit) (ev : FRDetEventSpec'' AM M abstract) : FRDetEventSpec AM M (α:=Unit) (β:=Unit) (α':=Unit) (β':=Unit) abstract :=
  {
    toEventSpec := ev.toEventSpec
    lift_in := id
    lift_out := id
    strengthening := fun m () => ev.strengthening m
    simulation := fun m () => ev.simulation m
  }

@[simp]
def newFRDetEvent'' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit)
  (ev : FRDetEventSpec'' AM M abs) : OrdinaryRDetEvent AM M Unit Unit:=
  newFRDetEvent abs ev.toFRDetEventSpec


/- Initialization events -/

structure InitFRDetEventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M]
  {α β α' β'} (abstract : InitNDEvent AM α' β')
  extends InitEventSpec M α β where

  lift_in : α → α'
  lift_out : β → β'

  strengthening (x : α):
    guard x
    → abstract.guard (lift_in x)

  simulation (x : α):
    (Hgrd : guard x)
    → let (y, m') := init x Hgrd
      abstract.init (lift_in x) (strengthening x Hgrd) (lift_out y, lift m')

@[simp]
def InitFRDetEventSpec.toInitRDetEventSpec  [Machine ACTX AM] [Machine CTX M] [instFR:FRefinement AM M]
  (abstract : InitNDEvent AM α' β')
  (ev : InitFRDetEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abstract) : InitRDetEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abstract :=
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
      exists (lift (ev.init x Hgrd).2)
  }

@[simp]
def newInitFRDetEvent [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : InitNDEvent AM α' β')
  (ev : InitFRDetEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : InitRDetEvent AM M α β α' β' :=
  newInitRDetEvent abs ev.toInitRDetEventSpec

structure InitFRDetEventSpec' (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M]
  {α α'} (abstract : InitNDEvent AM α' Unit)
  extends InitEventSpec' M α where

  lift_in : α → α'

  strengthening (x : α):
    guard x
    → abstract.guard (lift_in x)

  simulation (x : α):
    (Hgrd : guard x)
    → let m' := init x Hgrd
      abstract.init (lift_in x) (strengthening x Hgrd) ((), lift m')

@[simp]
def InitFRDetEventSpec'.toInitFRDetEventSpec  [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abstract : InitNDEvent AM α' Unit)
  (ev : InitFRDetEventSpec' AM M (α:=α) (α':=α') abstract) : InitFRDetEventSpec AM M (α:=α) (β:=Unit) (α':=α') (β':=Unit) abstract :=
  {
    toInitEventSpec := ev.toInitEventSpec
    lift_in := ev.lift_in
    lift_out := id
    strengthening := ev.strengthening
    simulation := ev.simulation
  }

@[simp]
def newInitFRDetEvent' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : InitNDEvent AM α' Unit)
  (ev : InitFRDetEventSpec' AM M (α:=α) (α':=α') abs) : InitRDetEvent AM M α Unit α' Unit :=
  newInitFRDetEvent abs ev.toInitFRDetEventSpec

structure InitFRDetEventSpec'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [FRefinement AM M]
  (abstract : InitNDEvent AM Unit Unit)
  extends InitEventSpec'' M where

  strengthening:
    guard
    → abstract.guard ()

  simulation:
    (Hgrd : guard)
    → let m' := init Hgrd
      abstract.init () (strengthening Hgrd) ((), lift m')

@[simp]
def InitFRDetEventSpec''.toInitFRDetEventSpec  [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abstract : InitNDEvent AM Unit Unit)
  (ev : InitFRDetEventSpec'' AM M abstract) : InitFRDetEventSpec AM M (α:=Unit) (β:=Unit) (α':=Unit) (β':=Unit) abstract :=
  {
    toInitEventSpec := ev.toInitEventSpec
    lift_in := id
    lift_out := id
    strengthening := fun () => ev.strengthening
    simulation := fun () => ev.simulation
  }

@[simp]
def newInitFRDetEvent'' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : InitNDEvent AM Unit Unit)
  (ev : InitFRDetEventSpec'' AM M abs) : InitRDetEvent AM M Unit Unit :=
  newInitFRDetEvent abs ev.toInitFRDetEventSpec
