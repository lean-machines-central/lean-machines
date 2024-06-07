
import LeanMachines.NonDet.Basic
import LeanMachines.NonDet.Ordinary
import LeanMachines.Refinement.Relational.Basic

open Refinement

structure _RNDEventPO  [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
   (ev : _NDEvent M α β) (kind : EventKind) (α' β')
   extends _NDEventPO ev kind where

  abstract : _NDEvent AM α' β'

  lift_in : α → α'
  lift_out : β → β'

  strengthening (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → ∀ am, refine am m
      → abstract.guard am (lift_in x)

  simulation (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → ∀ y, ∀ m', ev.effect m x (y, m')
      → ∀ am, refine am m
        → ∃ am', abstract.effect am (lift_in x) (lift_out y, am')
                 ∧ refine am' m'

structure OrdinaryRNDEvent (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  (α β) (α':=α) (β':=β) extends _NDEvent M α β where
  po : _RNDEventPO (instR:=instR) to_NDEvent (EventKind.TransNonDet Convergence.Ordinary) α' β'

@[simp]
def OrdinaryRNDEvent.toOrdinaryNDEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : OrdinaryRNDEvent AM M α β α' β') : OrdinaryNDEvent M α β :=
  {
    to_NDEvent := ev.to_NDEvent
    po := ev.po.to_NDEventPO
  }

structure RNDEventSpec (AM) [Machine ACTX AM]
                        (M) [Machine CTX M]
                        [Refinement AM M]
  {α β α' β'} (abstract : OrdinaryNDEvent AM α' β')
  extends NDEventSpec M α β where

  lift_in : α → α'
  lift_out : β → β'

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ am, refine am m
      → abstract.guard am (lift_in x)

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ y, ∀ m', effect m x (y, m')
      -- XXX : some constraint on output ?
      → ∀ am, refine am m
        → ∃ am', abstract.effect am (lift_in x) (lift_out y, am')
                 ∧ refine am' m'

@[simp]
def newRNDEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM α' β') (ev : RNDEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : OrdinaryRNDEvent AM M α β α' β' :=
  {
    to_NDEvent := ev.to_NDEvent
    po := {
      safety := ev.safety
      feasibility := ev.feasibility
      abstract := abs.to_NDEvent
      strengthening := ev.strengthening
      simulation := ev.simulation
    }
  }

structure RNDEventSpec' (AM) [Machine ACTX AM]
                        (M) [Machine CTX M]
                        [Refinement AM M]
  {α α'} (abstract : OrdinaryNDEvent AM α' Unit)
  extends NDEventSpec' M α where

  lift_in : α → α'

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ am, refine am m
      → abstract.guard am (lift_in x)

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ m', effect m x m'
      -- XXX : some constraint on output ?
      → ∀ am, refine am m
        → ∃ am', abstract.effect am (lift_in x) ((), am')
                 ∧ refine am' m'

@[simp]
def RNDEventSpec'.toRNDEventSpec [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  {α α'} (abs : OrdinaryNDEvent AM α' Unit) (ev : RNDEventSpec' AM M (α:=α) (α':=α') abs) : RNDEventSpec AM M (α:=α) (β:=Unit) (α':=α') (β':=Unit) abs :=
  {
    toNDEventSpec := ev.toNDEventSpec
    lift_in := ev.lift_in
    lift_out := id
    strengthening := ev.strengthening
    simulation := fun m x => by
      simp
      intros Hinv Hgrd _ m' Heff am Href
      apply ev.simulation m x Hinv Hgrd
      <;> assumption
  }

@[simp]
def newRNDEvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM α' Unit) (ev : RNDEventSpec' AM M (α:=α) (α':=α') abs) : OrdinaryRNDEvent AM M α Unit α' Unit :=
  newRNDEvent abs ev.toRNDEventSpec

structure RNDEventSpec'' (AM) [Machine ACTX AM]
                        (M) [Machine CTX M]
                        [Refinement AM M]
  (abstract : OrdinaryNDEvent AM Unit Unit)
  extends NDEventSpec'' M where

  strengthening (m : M):
    Machine.invariant m
    → guard m
    → ∀ am, refine am m
      → abstract.guard am ()

  simulation (m : M):
    Machine.invariant m
    → guard m
    → ∀ m', effect m m'
      → ∀ am, refine am m
        → ∃ am', abstract.effect am () ((), am')
                 ∧ refine am' m'

@[simp]
def RNDEventSpec''.toRNDEventSpec [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit) (ev : RNDEventSpec'' AM M abs) : RNDEventSpec AM M (α:=Unit) (β:=Unit) (α':=Unit) (β':=Unit) abs :=
  {
    toNDEventSpec := ev.toNDEventSpec
    lift_in := id
    lift_out := id
    strengthening := fun m () => ev.strengthening m
    simulation := fun m () => by
      simp
      intros Hinv Hgrd _ m' Heff am Href
      apply ev.simulation m Hinv Hgrd
      <;> assumption
  }

@[simp]
def newRNDEvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit) (ev : RNDEventSpec'' AM M abs) : OrdinaryRNDEvent AM M Unit Unit :=
  newRNDEvent abs ev.toRNDEventSpec

/- Initialization events -/

structure _InitRNDEventPO  [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
   (ev : _InitNDEvent M α β) (kind : EventKind) (α' β')
   extends _InitNDEventPO ev kind where

  abstract : _InitNDEvent AM α' β'

  lift_in : α → α'
  lift_out : β → β'

  strengthening (x : α):
    ev.guard x
    → abstract.guard (lift_in x)

  simulation (x : α):
    ev.guard x
    → ∀ y, ∀ m', ev.init x (y, m')
      → ∃ am', abstract.init (lift_in x) (lift_out y, am')
               ∧ refine am' m'

structure InitRNDEvent (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  (α) (β) (α':=α) (β':=β)
  extends _InitNDEvent M α β where
  po : _InitRNDEventPO (instR:=instR) to_InitNDEvent (EventKind.InitNonDet) α' β'

@[simp]
def InitRNDEvent.toInitNDEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (ev : InitRNDEvent AM M α β α' β') : InitNDEvent M α β :=
{
  to_InitNDEvent:= ev.to_InitNDEvent
  po := ev.po.to_InitNDEventPO
}

structure InitRNDEventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  {α β α' β'} (abstract : InitNDEvent AM α' β')
  extends InitNDEventSpec M α β where

  lift_in : α → α'
  lift_out : β → β'

  strengthening (x : α):
    guard x
    → abstract.guard (lift_in x)

  simulation (x : α):
    guard x
    → ∀ y, ∀ m', init x (y, m')
      → ∃ am', abstract.init (lift_in x) (lift_out y, am')
               ∧ refine am' m'

@[simp]
def newInitRNDEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  {α β α' β'} (abs : InitNDEvent AM α' β')
  (ev : InitRNDEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : InitRNDEvent AM M α β α' β' :=
  {
    to_InitNDEvent := (newInitNDEvent ev.toInitNDEventSpec).to_InitNDEvent
    po := {
      lift_in := ev.lift_in
      lift_out := ev.lift_out

      safety := fun x => by
        simp
        intros Hgrd y m' Hini
        apply ev.safety (y:=y) x Hgrd
        assumption

      feasibility := fun x => by
        simp
        intro Hgrd
        apply ev.feasibility x Hgrd

      abstract := abs.to_InitNDEvent

      strengthening := fun x => by
        simp
        intros Hgrd
        apply ev.strengthening x Hgrd

      simulation := fun x => by
        simp
        intro Hgrd y m' Hini
        apply ev.simulation x Hgrd y m' Hini
    }
  }

structure InitRNDEventSpec' (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  {α α'} (abstract : InitNDEvent AM α' Unit)
  extends InitNDEventSpec' M α where

  lift_in : α → α'

  strengthening (x : α):
    guard x
    → abstract.guard (lift_in x)

  simulation (x : α):
    guard x
    → ∀ m', init x m'
      → ∃ am', abstract.init (lift_in x) ((), am')
               ∧ refine am' m'

@[simp]
def InitRNDEventSpec'.toInitRNDEventSpec [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abstract : InitNDEvent AM α' Unit)
  (ev : InitRNDEventSpec' AM M (α:=α) (α':=α') abstract): InitRNDEventSpec AM M (α:=α) (β:=Unit) (α':=α') (β':=Unit) abstract :=
  {
    toInitNDEventSpec := ev.toInitNDEventSpec
    lift_in := ev.lift_in
    lift_out := id
    strengthening := fun x => by simp ; apply ev.strengthening
    simulation := fun x => by
      simp
      intros Hgrd _ m' Hini
      apply ev.simulation x Hgrd m' Hini
  }

@[simp]
def newInitRNDEvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  {α α'} (abs : InitNDEvent AM α' Unit)
  (ev : InitRNDEventSpec' AM M (α:=α) (α':=α') abs) : InitRNDEvent AM M α Unit α' Unit :=
  newInitRNDEvent abs ev.toInitRNDEventSpec

structure InitRNDEventSpec'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  (abstract : InitNDEvent AM Unit Unit)
  extends InitNDEventSpec'' M where

  strengthening:
    guard
    → abstract.guard ()

  simulation:
    guard
    → ∀ m', init m'
      → ∃ am', abstract.init () ((), am')
               ∧ refine am' m'

@[simp]
def InitRNDEventSpec''.toInitRNDEventSpec [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abstract : InitNDEvent AM Unit Unit)
  (ev : InitRNDEventSpec'' AM M abstract): InitRNDEventSpec AM M (α:=Unit) (β:=Unit) (α':=Unit) (β':=Unit) abstract :=
  {
    toInitNDEventSpec := ev.toInitNDEventSpec
    lift_in := id
    lift_out := id
    strengthening := fun x => by simp ; apply ev.strengthening
    simulation := fun x => by
      simp
      intros Hgrd _ m' Hini
      apply ev.simulation Hgrd m' Hini
  }

@[simp]
def newInitRNDEvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : InitNDEvent AM Unit Unit)
  (ev : InitRNDEventSpec'' AM M abs) : InitRNDEvent AM M Unit Unit :=
  newInitRNDEvent abs ev.toInitRNDEventSpec
