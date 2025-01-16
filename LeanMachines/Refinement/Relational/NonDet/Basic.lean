
import LeanMachines.NonDet.Basic
import LeanMachines.NonDet.Ordinary
import LeanMachines.Refinement.Relational.Basic

open Refinement
/-!

# Relational refinement of Non-deterministic events

This module contains the principles of relational refinement
for ordinary, non-deterministic events.

-/

/-!
## Ordinary non-deterministic events
-/

/-- Internal representation of proof obligations for ordinary non-deterministic events. -/
structure _RNDEventPO  [@Machine ACTX AM] [@Machine CTX M] [instR: Refinement AM M]
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
    (Hinv : Machine.invariant m)
    → (Hgrd : ev.guard m x)
    → ∀ y, ∀ m', ev.effect m x Hgrd (y, m')
      → ∀ am, (Href : refine am m)
        → ∃ am', abstract.effect am (lift_in x) (strengthening m x Hinv Hgrd am Href) (lift_out y, am')
                 ∧ refine am' m'

/-- The representation of ordinary refined non-deterministic events
with: `AM` the abstact machine type, `M` the concrete maching type,
 `α` the concrete input parameter type, `α'` the corresponding abstract input type (by default, `α`)
 `β` the concrete input parameter type, `β'` the corresponding abstract input type (by default, `β`)

Note that events, of type `OrdinaryRNDEvent`, are not directly constructed using this
structure. More user-friendly specification structures, such as `RNDEventSpec`, and smart constructors,
 such as `newRNDEvent` are preferably employed in practice.
 -/
structure OrdinaryRNDEvent (AM) [@Machine ACTX AM] (M) [@Machine CTX M] [instR: Refinement AM M]
  (α β) (α':=α) (β':=β) extends _NDEvent M α β where
  po : _RNDEventPO (instR:=instR) to_NDEvent (EventKind.TransNonDet Convergence.Ordinary) α' β'

@[simp]
def OrdinaryRNDEvent.toOrdinaryNDEvent [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (ev : OrdinaryRNDEvent AM M α β α' β') : OrdinaryNDEvent M α β :=
  {
    to_NDEvent := ev.to_NDEvent
    po := ev.po.to_NDEventPO
  }

/-- Specification of ordinary refined non-deterministic events.
with: `AM` the abstact machine type, `M` the concrete maching type,
 `α` the concrete input parameter type, `α'` the corresponding abstract input type (by default, `α`)
 `β` the concrete input parameter type, `β'` the corresponding abstract input type (by default, `β`)
The `abs` parameter is the ordinary non-deterministic event intended to be refined.

Note that `abs` should not be anticipated nor convergent.

The input and output types can be lifted to the abstract, if needed,
 using the `lift_in` and `lift_out` components.

The proof obligations, beyond `safety` and `feasibility` (of abstract events),
are guard `strengthening` and abstract event `simulation`.
 -/
structure RNDEventSpec (AM) [@Machine ACTX AM]
                        (M) [@Machine CTX M]
                        [Refinement AM M]
  {α β α' β'} (abstract : OrdinaryNDEvent AM α' β')
  extends NDEventSpec M α β where

  /-- Transformation of input parameters: how a concrete parameter must be interpreted
  at the abstract level. -/
  lift_in : α → α'

  /-- Transformation of output value: how a concrete output must be interpreted
  at the abstract level. -/
  lift_out : β → β'

  /-- Proof obligation: guard strengthening. -/
  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ am, refine am m
      → abstract.guard am (lift_in x)

  /-- Proof obligation: action simulation. -/
  simulation (m : M) (x : α):
    (Hinv : Machine.invariant m)
    → (Hgrd : guard m x)
    → ∀ y, ∀ m', effect m x Hgrd (y, m')
      -- XXX : some constraint on output ?
      → ∀ am, (Href : refine am m)
        → ∃ am', abstract.effect am (lift_in x) (strengthening m x Hinv Hgrd am Href) (lift_out y, am')
                 ∧ refine am' m'

/-- Smart constructor for ordinary refined non-deterministic event,
with: `abs` the (ordinary) non-deterministic event to refine, and
  `ev` the refined event specification (cf. `RNDEventSpec`).
-/
@[simp]
def newRNDEvent [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
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

/-- Variant of `RNDEventSpec` with implicit `Unit` output type -/
structure RNDEventSpec' (AM) [@Machine ACTX AM]
                        (M) [@Machine CTX M]
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
    (Hinv : Machine.invariant m)
    → (Hgrd : guard m x)
    → ∀ m', effect m x Hgrd m'
      -- XXX : some constraint on output ?
      → ∀ am, (Href : refine am m)
        → ∃ am', abstract.effect am (lift_in x) (strengthening m x Hinv Hgrd am Href) ((), am')
                 ∧ refine am' m'

@[simp]
def RNDEventSpec'.toRNDEventSpec [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
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

/-- Variant of `newRNDEvent` with implicit `Unit` output type -/
@[simp]
def newRNDEvent' [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM α' Unit) (ev : RNDEventSpec' AM M (α:=α) (α':=α') abs) : OrdinaryRNDEvent AM M α Unit α' Unit :=
  newRNDEvent abs ev.toRNDEventSpec

/-- Variant of `RNDEventSpec` with implicit `Unit` input and output types -/
structure RNDEventSpec'' (AM) [@Machine ACTX AM]
                        (M) [@Machine CTX M]
                        [Refinement AM M]
  (abstract : OrdinaryNDEvent AM Unit Unit)
  extends NDEventSpec'' M where

  strengthening (m : M):
    Machine.invariant m
    → guard m
    → ∀ am, refine am m
      → abstract.guard am ()

  simulation (m : M):
    (Hinv : Machine.invariant m)
    → (Hgrd : guard m)
    → ∀ m', effect m Hgrd m'
      → ∀ am, (Href : refine am m)
        → ∃ am', abstract.effect am () (strengthening m Hinv Hgrd am Href) ((), am')
                 ∧ refine am' m'

@[simp]
def RNDEventSpec''.toRNDEventSpec [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
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

/-- Variant of `newRNDEvent` with implicit `Unit` input and output types -/
@[simp]
def newRNDEvent'' [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit) (ev : RNDEventSpec'' AM M abs) : OrdinaryRNDEvent AM M Unit Unit :=
  newRNDEvent abs ev.toRNDEventSpec

/-!
## Non-deterministic initialization events
-/

/-- Internal representation of proof obligations for ordinary initialization events. -/
structure _InitRNDEventPO  [@Machine ACTX AM] [@Machine CTX M] [instR: Refinement AM M]
   (ev : _InitNDEvent M α β) (kind : EventKind) (α' β')
   extends _InitNDEventPO ev kind where

  abstract : _InitNDEvent AM α' β'

  lift_in : α → α'
  lift_out : β → β'

  strengthening (x : α):
    ev.guard x
    → abstract.guard (lift_in x)

  simulation (x : α):
    (Hgrd : ev.guard x)
    → ∀ y, ∀ m', ev.init x Hgrd (y, m')
      → ∃ am', abstract.init (lift_in x) (strengthening x Hgrd) (lift_out y, am')
               ∧ refine am' m'

/-- The (internal) type of ordinary refined non-deterministic initialization events
with: `AM` the abstact machine type, `M` the concrete maching type,
 `α` the concrete input parameter type, `α'` the corresponding abstract input type (by default, `α`)
 `β` the concrete input parameter type, `β'` the corresponding abstract input type (by default, `β`) -/
structure InitRNDEvent (AM) [@Machine ACTX AM] (M) [@Machine CTX M] [instR: Refinement AM M]
  (α) (β) (α':=α) (β':=β)
  extends _InitNDEvent M α β where
  po : _InitRNDEventPO (instR:=instR) to_InitNDEvent (EventKind.InitNonDet) α' β'

@[simp]
def InitRNDEvent.toInitNDEvent [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M] (ev : InitRNDEvent AM M α β α' β') : InitNDEvent M α β :=
{
  to_InitNDEvent:= ev.to_InitNDEvent
  po := ev.po.to_InitNDEventPO
}

/-- Specification of ordinary refined initialization events.
The proof obligations, beyond `safety` and `feasibility` are guard `strengthening`
and abstract event `simulation`.

The input and output types can be lifted to the abstract, if needed,
 using the `lift_in` and `lift_out` components.
 -/
structure InitRNDEventSpec (AM) [@Machine ACTX AM] (M) [@Machine CTX M] [Refinement AM M]
  {α β α' β'} (abstract : InitNDEvent AM α' β')
  extends InitNDEventSpec M α β where

  lift_in : α → α'
  lift_out : β → β'

  strengthening (x : α):
    guard x
    → abstract.guard (lift_in x)

  simulation (x : α):
    (Hgrd : guard x)
    → ∀ y, ∀ m', init x Hgrd (y, m')
      → ∃ am', abstract.init (lift_in x) (strengthening x Hgrd) (lift_out y, am')
               ∧ refine am' m'

/-- Smart constructor for non-deterministic refined initialization event,
with: `abs` the (ordinary) event to refine, and
  `ev` the refined event specification (cf. `InitRNDEventSpec`).
-/
@[simp]
def newInitRNDEvent [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
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

/-- Variant of `InitRNDEventSpec` with implicit `Unit` output type -/
structure InitRNDEventSpec' (AM) [@Machine ACTX AM] (M) [@Machine CTX M] [Refinement AM M]
  {α α'} (abstract : InitNDEvent AM α' Unit)
  extends InitNDEventSpec' M α where

  lift_in : α → α'

  strengthening (x : α):
    guard x
    → abstract.guard (lift_in x)

  simulation (x : α):
    (Hgrd : guard x)
    → ∀ m', init x Hgrd m'
      → ∃ am', abstract.init (lift_in x) (strengthening x Hgrd) ((), am')
               ∧ refine am' m'

@[simp]
def InitRNDEventSpec'.toInitRNDEventSpec [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
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

/-- Variant of `newInitRNDEvent` with implicit `Unit` output type -/
@[simp]
def newInitRNDEvent' [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  {α α'} (abs : InitNDEvent AM α' Unit)
  (ev : InitRNDEventSpec' AM M (α:=α) (α':=α') abs) : InitRNDEvent AM M α Unit α' Unit :=
  newInitRNDEvent abs ev.toInitRNDEventSpec

/-- Variant of `InitRNDEventSpec` with implicit `Unit` input and output types -/
structure InitRNDEventSpec'' (AM) [@Machine ACTX AM] (M) [@Machine CTX M] [Refinement AM M]
  (abstract : InitNDEvent AM Unit Unit)
  extends InitNDEventSpec'' M where

  strengthening:
    guard
    → abstract.guard ()

  simulation:
    (Hgrd : guard)
    → ∀ m', init Hgrd m'
      → ∃ am', abstract.init () (strengthening Hgrd) ((), am')
               ∧ refine am' m'

@[simp]
def InitRNDEventSpec''.toInitRNDEventSpec [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
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

/-- Variant of `newInitRNDEvent` with implicit `Unit` input and output types -/
@[simp]
def newInitRNDEvent'' [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (abs : InitNDEvent AM Unit Unit)
  (ev : InitRNDEventSpec'' AM M abs) : InitRNDEvent AM M Unit Unit :=
  newInitRNDEvent abs ev.toInitRNDEventSpec
