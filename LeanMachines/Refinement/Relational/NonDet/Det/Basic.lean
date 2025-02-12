
import LeanMachines.Refinement.Relational.Basic
import LeanMachines.NonDet.Ordinary

open Refinement

/-!

# Deterministic refined event from non-deterministic abstract events

This module defines the construction of deterministic events that
refine non-determistic abstract events.

-/

/-- The internal representation of the proof obligations for deterministic
refined events. -/
structure _RDetEventPO  [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
   (ev : _Event M α β) (kind : EventKind) (α' β')
   extends _EventPO ev kind where

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
    → ∀ am, (Href : refine am m)
      → let (y, m') := ev.action m x Hgrd
        ∃ am', abstract.effect am (lift_in x) (strengthening m x Hinv Hgrd am Href) (lift_out y, am')
               ∧ refine am' m'

/-- The representation of ordinary deterministic refined events
with: `AM` the abstact machine type, `M` the concrete maching type,
 `α` the concrete input parameter type, `α'` the corresponding abstract input type (by default, `α`)
 `β` the concrete input parameter type, `β'` the corresponding abstract input type (by default, `β`)

Note that events, of type `OrdinaryRDetEvent`, are not directly constructed using this
structure. More user-friendly specification structures, such as `RDetEventSpec`, and smart constructors,
 such as `newRDetEvent` are preferably employed in practice.
 -/
structure OrdinaryRDetEvent (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  (α) (β) (α':=α) (β':=β) extends _Event M α β where
  po : _RDetEventPO (instR:=instR) to_Event (EventKind.TransDet Convergence.Ordinary) α' β'

@[simp]
def OrdinaryRDetEvent.toOrdinaryEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : OrdinaryRDetEvent AM M α β α' β') : OrdinaryEvent M α β :=
  {
    to_Event := ev.to_Event
    po := ev.po.to_EventPO
  }

/-- Specification of ordinary deterministic refined events.
with: `AM` the abstact machine type, `M` the concrete maching type,
 `α` the concrete input parameter type, `α'` the corresponding abstract input type (by default, `α`)
 `β` the concrete input parameter type, `β'` the corresponding abstract input type (by default, `β`)
The `abs` parameter is the ordinary non-deterministic event intended to be refined.

Note that `abs` should not be anticipated nor convergent.

The input and output types can be lifted to the abstract, if needed,
 using the `lift_in` and `lift_out` components.

The proof obligations, beyond `safety` are guard `strengthening`
and abstract event `simulation`,  cf. `REventSpec`.
 -/
structure RDetEventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  {α β α' β'} (abstract : OrdinaryNDEvent AM α' β')
  extends EventSpec M α β where

  lift_in : α → α'
  lift_out : β → β'

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ am, refine am m
      → abstract.guard am (lift_in x)

  simulation (m : M) (x : α):
    (Hinv : Machine.invariant m)
    → (Hgrd : guard m x)
    → ∀ am, (Href : refine am m)
      → let (y, m') := action m x Hgrd
        ∃ am', abstract.effect am (lift_in x) (strengthening m x Hinv Hgrd am Href) (lift_out y, am')
               ∧ refine am' m'

/-- Smart constructor for ordinary deterministic refined event,
with: `abs` the (ordinary) non-deterministic event to refine, and
  `ev` the refined event specification (cf. `RDetEventSpec`).
-/
@[simp]
def newRDetEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM α' β') (ev : RDetEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : OrdinaryRDetEvent AM M α β α' β' :=
  {
    to_Event := ev.to_Event
    po := {
      safety := ev.safety
      abstract := abs.to_NDEvent
      strengthening := ev.strengthening
      simulation := ev.simulation
    }
  }

/-- Variant of `RDetEventSpec` with implicit `Unit` output type -/
structure RDetEventSpec' (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  {α α'} (abstract : OrdinaryNDEvent AM α' Unit)
  extends EventSpec' M α where

  lift_in : α → α'

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ am, refine am m
      → abstract.guard am (lift_in x)

  simulation (m : M) (x : α):
    (Hinv : Machine.invariant m)
    → (Hgrd : guard m x)
    → ∀ am, (Href : refine am m)
      → let m' := action m x Hgrd
        ∃ am', abstract.effect am (lift_in x) (strengthening m x Hinv Hgrd am Href) ((), am')
               ∧ refine am' m'

@[simp]
def RDetEventSpec'.toRDetEventSpec [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abstract : OrdinaryNDEvent AM α' Unit)
  (ev : RDetEventSpec' AM M (α:=α) (α':=α') abstract) : RDetEventSpec AM M (α:=α) (β:=Unit) (α':=α') (β':=Unit) abstract :=
  {
    toEventSpec := ev.toEventSpec
    lift_in := ev.lift_in
    lift_out := id
    strengthening := ev.strengthening
    simulation := ev.simulation
  }

/-- Variant of `newRDetEvent` with implicit `Unit` output type -/
@[simp]
def newRDetEvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM α' Unit) (ev : RDetEventSpec' AM M (α:=α) (α':=α') abs) : OrdinaryRDetEvent AM M α Unit α' Unit :=
  newRDetEvent abs ev.toRDetEventSpec

/-- Variant of `RDetEventSpec` with implicit `Unit` input and output types -/
structure RDetEventSpec'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  (abstract : OrdinaryNDEvent AM Unit Unit)
  extends EventSpec'' M where

  strengthening (m : M):
    Machine.invariant m
    → guard m
    → ∀ am, refine am m
      → abstract.guard am ()

  simulation (m : M):
    (Hinv : Machine.invariant m)
    → (Hgrd : guard m)
    → ∀ am, (Href : refine am m)
      → let m' := action m Hgrd
        ∃ am', abstract.effect am () (strengthening m Hinv Hgrd am Href) ((), am')
               ∧ refine am' m'

@[simp]
def RDetEventSpec''.toRDetEventSpec [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abstract : OrdinaryNDEvent AM Unit Unit)
  (ev : RDetEventSpec'' AM M abstract) : RDetEventSpec AM M (α:=Unit) (β:=Unit) (α':=Unit) (β':=Unit) abstract :=
  {
    toEventSpec := ev.toEventSpec
    lift_in := id
    lift_out := id
    strengthening := fun m () => ev.strengthening m
    simulation := fun m () => ev.simulation m
  }

/-- Variant of `newRDetEvent` with implicit `Unit` input and output types -/
@[simp]
def newRDetEvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit) (ev : RDetEventSpec'' AM M abs) : OrdinaryRDetEvent AM M Unit Unit :=
  newRDetEvent abs ev.toRDetEventSpec

/-!
### Ordinary initialization events
-/

/-- Internal representation of proof obligations for ordinary deterministic
initialization events. -/
structure _InitRDetEventPO  [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
   (ev : _InitEvent M α β) (kind : EventKind) (α' β')
   extends _InitEventPO ev kind where

  abstract : InitNDEvent AM α' β'

  lift_in : α → α'
  lift_out : β → β'

  strengthening (x : α):
    ev.guard x
    → abstract.guard (lift_in x)

  simulation (x : α):
    (Hgrd : ev.guard x)
    → let (y, m') := ev.init x Hgrd
      ∃ am', abstract.init (lift_in x) (strengthening x Hgrd) (lift_out y, am')
             ∧ refine am' m'

/-- The (internal) type of ordinary deterministic refined initialization events
with: `AM` the abstact machine type, `M` the concrete maching type,
 `α` the concrete input parameter type, `α'` the corresponding abstract input type (by default, `α`)
 `β` the concrete input parameter type, `β'` the corresponding abstract input type (by default, `β`) -/
structure InitRDetEvent (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  (α) (β) (α':=α) (β':=β) extends _InitEvent M α β where
  po : _InitRDetEventPO (instR:=instR) to_InitEvent EventKind.InitDet α' β'

@[simp]
def InitRDetEvent.toInitEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : InitRDetEvent AM M α β α' β') : InitEvent M α β :=
  {
    to_InitEvent := ev.to_InitEvent
    po := ev.po.to_InitEventPO
  }

/-- Specification of ordinary deterministic refined initialization events.
The proof obligations, beyond `safety` are guard `strengthening`
and abstract event `simulation`.

The input and output types can be lifted to the abstract, if needed,
 using the `lift_in` and `lift_out` components.
 -/
structure InitRDetEventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
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
      ∃ am', abstract.init (lift_in x) (strengthening x Hgrd) (lift_out y, am')
              ∧ refine am' m'

/-- Smart constructor for ordinary deterministic refined initialization event,
with: `abs` the (ordinary) non-deterministic event to refine, and
  `ev` the refined event specification (cf. `InitREventSpec`).
-/
@[simp]
def newInitRDetEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : InitNDEvent AM α' β') (ev : InitRDetEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : InitRDetEvent AM M α β α' β' :=
  {
    to_InitEvent := ev.to_InitEvent
    po := {
      lift_in := ev.lift_in
      lift_out := ev.lift_out
      safety := fun x => by simp ; apply ev.safety
      abstract := abs
      strengthening := fun x => by
        simp
        intros Hgrd
        apply ev.strengthening x Hgrd

      simulation := fun x => by
        simp
        intros Hgrd
        have Hsim := ev.simulation x Hgrd
        simp at Hsim
        obtain ⟨am', Hsim₁, Hsim₂⟩ := Hsim
        exists am'
    }
  }

/-- Variant of `InitRDetEventSpec` with implicit `Unit` output type -/
structure InitRDetEventSpec' (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  {α α'} (abstract : InitNDEvent AM α' Unit)
  extends InitEventSpec' M α where

  lift_in : α → α'

  strengthening (x : α):
    guard x
    → abstract.guard (lift_in x)

  simulation (x : α):
    (Hgrd : guard x)
    → let m' := init x Hgrd
      ∃ am', abstract.init (lift_in x) (strengthening x Hgrd)  ((), am')
              ∧ refine am' m'

@[simp]
def InitRDetEventSpec'.toInitRDetEventSpec [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abstract : InitNDEvent AM α' Unit)
  (ev : InitRDetEventSpec' AM M (α:=α) (α':=α') abstract) : InitRDetEventSpec AM M (α:=α) (β:=Unit) (α':=α') (β':=Unit) abstract :=
  {
    toInitEventSpec := ev.toInitEventSpec
    lift_in := ev.lift_in
    lift_out := id
    strengthening := ev.strengthening
    simulation := ev.simulation
  }

/-- Variant of `newInitRDetEvent` with implicit `Unit` output type -/
@[simp]
def newInitRDetEvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : InitNDEvent AM α' Unit) (ev : InitRDetEventSpec' AM M (α:=α) (α':=α') abs) : InitRDetEvent AM M α Unit α' Unit :=
  newInitRDetEvent abs ev.toInitRDetEventSpec

/-- Variant of `InitRDetEventSpec` with implicit `Unit` input and output types -/
structure InitRDetEventSpec'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  (abstract : InitNDEvent AM Unit Unit)
  extends InitEventSpec'' M where

  strengthening:
    guard
    → abstract.guard ()

  simulation:
    (Hgrd : guard)
    → let m' := init Hgrd
      ∃ am', abstract.init () (strengthening Hgrd) ((), am')
              ∧ refine am' m'

@[simp]
def InitRDetEventSpec''.toInitRDetEventSpec [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abstract : InitNDEvent AM Unit Unit)
  (ev : InitRDetEventSpec'' AM M abstract) : InitRDetEventSpec AM M (α:=Unit) (β:=Unit) (α':=Unit) (β':=Unit) abstract :=
  {
    toInitEventSpec := ev.toInitEventSpec
    lift_in := id
    lift_out := id
    strengthening := fun () => ev.strengthening
    simulation := fun () => ev.simulation
  }

/-- Variant of `newRDetEvent` with implicit `Unit` input and output types -/
@[simp]
def newInitRDetEvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : InitNDEvent AM Unit Unit) (ev : InitRDetEventSpec'' AM M abs) : InitRDetEvent AM M Unit Unit :=
  newInitRDetEvent abs ev.toInitRDetEventSpec
