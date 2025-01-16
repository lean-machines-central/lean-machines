
import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary
import LeanMachines.Event.Convergent

/-!

# Relational refinement

This module contains the basic definitions of the relational
refinement principles for LeanMachines.

This is heavily inspired by the Event-B refinement principles
with some slight differences:

  - concrete events are not obligatory convergent (but may be, of course)
  - event merging is only indirectly supported
  - events can be composed in various ways, and machines do not directly
    integrate events.
  - alternative (and compatible) refinement principles may be (and are) proposed

-/

/-!

## Machine refinement

-/

/-- The typeclass definition for the functional refinement
of an abstract machine type `AM` (in context `ACTX`) by
 a (more) concrete machine type `M` (in context `CTX`).
-/

class Refinement {ACTX : outParam (Type u₁)} (AM)
                 [@Machine ACTX AM]
                 {CTX : outParam (Type u₂)} (M)
                 [@Machine CTX M] where

  /-- The relation between the abstract machine type `AM` and
   the concrete machine type `M`, defined as a type-theoretic proposition. -/
  refine : AM → M → Prop

  /-- The safety requirement of refinement. -/
  refine_safe (am : AM) (m : M):
    Machine.invariant m
    → refine am m
    → Machine.invariant am

open Refinement

/-!

## Event refinement

### Ordinary transitional events

-/

/-- Internal representation of proof obligations for ordinary events. -/
structure _REventPO  [@Machine ACTX AM] [@Machine CTX M] [instR: Refinement AM M]
   (ev : _Event M α β) (kind : EventKind) (α' β')
   extends _EventPO ev kind where

  abstract : _Event AM α' β'

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
    → ∀ am, (Href: refine am m)
      -- XXX : some constraint on output ?
      --       (maybe a post_weakening requirement ?)
      --       for now, let's go with equality because its transparent for the Event-B
      --       refinement model
      → let (y, m') := ev.action m x Hgrd
        let (z, am') := abstract.action am (lift_in x) (strengthening m x Hinv Hgrd am Href)
        lift_out y = z ∧ refine am' m'

/-- The representation of ordinary refined events
with: `AM` the abstact machine type, `M` the concrete maching type,
 `α` the concrete input parameter type, `α'` the corresponding abstract input type (by default, `α`)
 `β` the concrete input parameter type, `β'` the corresponding abstract input type (by default, `β`)

Note that events, of type `OrdinaryREvent`, are not directly constructed using this
structure. More user-friendly specification structures, such as `REventSpec`, and smart constructors,
 such as `newREvent` are preferably employed in practice.
 -/
structure OrdinaryREvent (AM) [@Machine ACTX AM] (M) [@Machine CTX M] [instR: Refinement AM M]
  (α β) (α':=α) (β':=β) extends _Event M α β where
  po : _REventPO (instR:=instR) to_Event (EventKind.TransDet Convergence.Ordinary) α' β'

@[simp]
def OrdinaryREvent.toOrdinaryEvent [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (ev : OrdinaryREvent AM M α β α' β') : OrdinaryEvent M α β :=
  {
    to_Event := ev.to_Event
    po := ev.po.to_EventPO
  }

/-- Specification of ordinary refined events.
with: `AM` the abstact machine type, `M` the concrete maching type,
 `α` the concrete input parameter type, `α'` the corresponding abstract input type (by default, `α`)
 `β` the concrete input parameter type, `β'` the corresponding abstract input type (by default, `β`)
The `abs` parameter is the ordinary event intended to be refined.

Note that `abs` should not be anticipated nor convergent.

The input and output types can be lifted to the abstract, if needed,
 using the `lift_in` and `lift_out` components.

The proof obligations, beyond `safety` (of abstract events) are guard `strengthening`
and abstract event `simulation`.
 -/
structure REventSpec (AM) [@Machine ACTX AM] (M) [@Machine CTX M] [instR: Refinement AM M]
  {α β α' β'} (abs : OrdinaryEvent AM α' β')
  extends EventSpec M α β where

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
      → abs.guard am (lift_in x)

  /-- Proof obligation: action simulation. -/
  simulation (m : M) (x : α):
    (Hinv : Machine.invariant m)
    → (Hgrd : guard m x)
    → ∀ am, (Href : refine am m)
      → let (y, m') := action m x Hgrd
        let (z, am') := abs.action am (lift_in x) (strengthening m x Hinv Hgrd am Href)
        lift_out y = z ∧ refine am' m'


/-- Smart constructor for ordinary refined event,
with: `abs` the (ordinary) event to refine, and
  `ev` the refined event specification (cf. `REventSpec`).
-/
@[simp]
def newREvent [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM α' β') (ev : REventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : OrdinaryREvent AM M α β α' β' :=
  {
    to_Event := ev.to_Event
    po := {
      safety := ev.safety
      abstract := abs.to_Event
      strengthening := ev.strengthening
      simulation := ev.simulation
    }
  }

/-- Variant of `REventSpec` with implicit `Unit` output type -/
structure REventSpec' (AM) [@Machine ACTX AM] (M) [@Machine CTX M] [instR: Refinement AM M]
  {α α'} (abstract : OrdinaryEvent AM α' Unit)
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
        let ((), am') := abstract.action am (lift_in x) (strengthening m x Hinv Hgrd am Href)
        refine am' m'

@[simp]
def REventSpec'.toREventSpec [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM α' Unit) (ev : REventSpec' AM M (α:=α) (α':=α') abs) : REventSpec AM M (α:=α) (β:=Unit) (α':=α') (β':=Unit) abs :=
  {
    toEventSpec := ev.toEventSpec
    lift_in := ev.lift_in
    lift_out := id
    strengthening := ev.strengthening
    simulation := fun m x => by simp ; apply ev.simulation m x
  }

/-- Variant of `newREvent` with implicit `Unit` output type -/
@[simp]
def newREvent' [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM α' Unit) (ev : REventSpec' AM M (α:=α) (α':=α') abs) : OrdinaryREvent AM M α Unit α' Unit :=
  newREvent abs ev.toREventSpec

/-- Variant of `REventSpec` with implicit `Unit` input and output types -/
structure REventSpec'' (AM) [@Machine ACTX AM] (M) [@Machine CTX M] [instR: Refinement AM M]
  (abstract : OrdinaryEvent AM Unit Unit)
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
        let ((), am') := abstract.action am () (strengthening m Hinv Hgrd am Href)
        refine am' m'

@[simp]
def REventSpec''.toREventSpec [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM Unit Unit) (ev : REventSpec'' AM M abs) : REventSpec AM M (α:=Unit) (β:=Unit) (α':=Unit) (β':=Unit) abs :=
  {
    toEventSpec := ev.toEventSpec
    lift_in := id
    lift_out := id
    strengthening := fun m x => by simp ; apply ev.strengthening m
    simulation := fun m x => by simp ; apply ev.simulation m
  }

/-- Variant of `newREvent` with implicit `Unit` input and output types -/
@[simp]
def newREvent'' [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM Unit Unit) (ev : REventSpec'' AM M abs) : OrdinaryREvent AM M Unit Unit :=
  newREvent abs ev.toREventSpec

/-!
### Ordinary initialization events
-/

/-- Internal representation of proof obligations for ordinary initialization events. -/
structure _InitREventPO  [@Machine ACTX AM] [@Machine CTX M] [instR: Refinement AM M]
   (ev : _InitEvent M α β) (kind : EventKind) (α' β')
   extends _InitEventPO ev kind where

  abstract : _InitEvent AM α' β'

  lift_in : α → α'
  lift_out : β → β'

  strengthening (x : α):
    ev.guard x
    → abstract.guard (lift_in x)

  simulation (x : α):
      (Hgrd : ev.guard x)
    → let (y, m') := ev.init x Hgrd
      let (z, am') := abstract.init (lift_in x) (strengthening x Hgrd)
      lift_out y = z ∧ refine am' m'

/-- The (internal) type of ordinary refined initialization events
with: `AM` the abstact machine type, `M` the concrete maching type,
 `α` the concrete input parameter type, `α'` the corresponding abstract input type (by default, `α`)
 `β` the concrete input parameter type, `β'` the corresponding abstract input type (by default, `β`) -/
structure InitREvent (AM) [@Machine ACTX AM] (M) [@Machine CTX M] [instR: Refinement AM M]
  (α) (β) (α':=α) (β':=β)
  extends _InitEvent M α β where
  po : _InitREventPO (instR:=instR) to_InitEvent (EventKind.InitDet) α' β'

@[simp]
def InitREvent.toInitEvent [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M] (ev : InitREvent AM M α β α' β') : InitEvent M α β :=
{
  to_InitEvent:= ev.to_InitEvent
  po := ev.po.to_InitEventPO
}

/-- Specification of ordinary refined initialization events.
The proof obligations, beyond `safety` are guard `strengthening`
and abstract event `simulation`.

The input and output types can be lifted to the abstract, if needed,
 using the `lift_in` and `lift_out` components.
 -/
structure InitREventSpec (AM) [@Machine ACTX AM] (M) [@Machine CTX M] [instR: Refinement AM M]
  {α β α' β'} (abstract : InitEvent AM α' β')
  extends InitEventSpec M α β where

  lift_in : α → α'
  lift_out : β → β'

  strengthening (x : α):
    guard x
    → abstract.guard (lift_in x)

  simulation (x : α):
    (Hgrd : guard x)
    → let (y, m') := init x Hgrd
      let (z, am') := abstract.init (lift_in x) (strengthening x Hgrd)
      lift_out y = z ∧ refine am' m'

/-- Smart constructor for ordinary refined initialization event,
with: `abs` the (ordinary) event to refine, and
  `ev` the refined event specification (cf. `InitREventSpec`).
-/
@[simp]
def newInitREvent [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (abs : InitEvent AM α' β')
  (ev : InitREventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : InitREvent AM M α β α' β' :=
  {
    to_InitEvent := ev.to_InitEvent
    po := {
      lift_in := ev.lift_in
      lift_out := ev.lift_out
      safety := fun x => by simp
                            intros Hgrd
                            apply ev.safety x Hgrd
      abstract := abs.to_InitEvent
      strengthening := fun x => by
        simp
        intros Hgrd
        apply ev.strengthening x Hgrd

      simulation := fun x => by
        simp
        intros Hgrd
        have Hsim := ev.simulation x Hgrd
        simp at Hsim
        assumption
    }
  }

/-- Variant of `InitREventSpec` with implicit `Unit` output type -/
structure InitREventSpec' (AM) [@Machine ACTX AM] (M) [@Machine CTX M] [instR: Refinement AM M]
  {α α'} (abstract : InitEvent AM α' Unit)
  extends InitEventSpec' M α where

  lift_in : α → α'

  strengthening (x : α):
    guard x
    → abstract.guard (lift_in x)

  simulation (x : α):
    (Hgrd : guard x)
    → let m' := init x Hgrd
      let ((), am') := abstract.init (lift_in x) (strengthening x Hgrd)
      refine am' m'

@[simp]
def InitREventSpec'.toInitREventSpec [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (abs : InitEvent AM α' Unit) (ev : InitREventSpec' AM M (α:=α) (α':=α') abs) : InitREventSpec AM M (α:=α) (β:=Unit) (α':=α') (β':=Unit) abs :=
  {
    toInitEventSpec := ev.toInitEventSpec
    lift_in := ev.lift_in
    lift_out := id
    strengthening := fun x => by simp ; apply ev.strengthening
    simulation := fun x => by simp ; apply ev.simulation
  }

/-- Variant of `newInitREvent` with implicit `Unit` output type -/
@[simp]
def newInitREvent' [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (abs : InitEvent AM α' Unit)
  (ev : InitREventSpec' AM M (α:=α) (α':=α') abs) : InitREvent AM M α Unit α' Unit :=
  newInitREvent abs ev.toInitREventSpec

/-- Variant of `InitREventSpec` with implicit `Unit` input and output types -/
structure InitREventSpec'' (AM) [@Machine ACTX AM] (M) [@Machine CTX M] [instR: Refinement AM M]
  (abstract : InitEvent AM Unit Unit)
  extends InitEventSpec'' M where

  strengthening:
    guard
    → abstract.guard ()

  simulation:
    (Hgrd : guard)
    → let m' := init grd
      let ((), am') := abstract.init () (strengthening Hgrd)
      refine am' m'

@[simp]
def InitREventSpec''.toInitREventSpec [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (abs : InitEvent AM Unit Unit) (ev : InitREventSpec'' AM M abs) : InitREventSpec AM M (α:=Unit) (β:=Unit) (α':=Unit) (β':=Unit) abs :=
  {
    toInitEventSpec := ev.toInitEventSpec
    lift_in := id
    lift_out := id
    strengthening := fun () => by simp ; apply ev.strengthening
    simulation := fun () Hgrd => by simp ; apply ev.simulation Hgrd
  }

/-- Variant of `newREvent` with implicit `Unit` input and output types -/
@[simp]
def newInitREvent'' [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (abs : InitEvent AM Unit Unit)
  (ev : InitREventSpec'' AM M abs) : InitREvent AM M Unit Unit :=
  newInitREvent abs ev.toInitREventSpec
