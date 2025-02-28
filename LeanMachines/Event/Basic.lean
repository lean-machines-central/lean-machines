import LeanMachines.Event.Prelude
import LeanMachines.Algebra.Contravariant
import LeanMachines.Algebra.Profunctor
import LeanMachines.Algebra.Arrow

/-!

# Basic definitions

This module contains the basic definitions of the LeanMachines
framework:

 - Machine types, instances of the `Machine` typeclass
 - Events, elements of the type `Event`.

 Note that the user-level specifications of events are
 defined in the modules `Ordinary` (for ordinary events)
  and `Convergent` (for anticipated and convergent events).

-/

/-!

## Machine types

-/

/-- The main definition of a **Machine** type, i.e. a state-based
 specification of a **system** (software, hardware model, ...).

This comprises:

 - a `context` of type `CTX`, allowing the machine to depend upon a
 mathematical context, in particular **static parameters** and related
 properties.

 - an `invariant` property defining the overall safety requirements of
 the machine states.

 - a `default` state, that defines the (unique) state of the machine before
 its initialization (very often, this is the default initialization state,
  but it can also be an unreachable "pre-init" state if required).

-/

class Machine (CTX : outParam (Type u)) (M) where
  /-- The context (i.e. parameters) of the machine. -/
  context : CTX
  /-- The invariant property that must be satisfied
  by a machine (state) of type `M`. -/
  invariant : M → Prop

/-- Enumeration for event kinds (ordinary, anticipated or convergent). -/
inductive Convergence where
  | Ordinary
  | Anticipated
  | Convergent
  deriving Repr, BEq, DecidableEq

/-- Event kinds: initialization or transitional,
 deterministic or non-deterministic,
 ordinary, anticipated or convergent. -/
inductive EventKind where
  | InitDet
  | InitNonDet
  | TransDet (status : Convergence)
  | TransNonDet (status : Convergence)
  deriving Repr, BEq, DecidableEq

def EventKind.is_init k :=
  match k with
  | InitDet | InitNonDet => true
  | _ => false

def EventKind.get_status k :=
  match k with
  | InitDet | InitNonDet => Convergence.Ordinary
  | TransDet s | TransNonDet s => s

def EventKind.refine? (kconcr : EventKind) (kabs :EventKind) : Bool :=
  (is_init kconcr = is_init kabs)
  &&
  match get_status kabs, get_status kconcr with
  | Convergence.Convergent, Convergence.Ordinary => false
  | Convergence.Convergent, Convergence.Anticipated => false
  | Convergence.Anticipated, Convergence.Ordinary => false
  | _ ,_ => true

open EventKind

/-!
## Deterministic events (internal representation)
-/

/-- The internal representation of all *deterministic* transitional events
with: `M` the machine type,
`α` the input type, and `β` the output type of the event
This extends `_EventRoot` with a notion of (deterministic/functional) action.
.-/
@[ext]
structure Event (M) [Machine CTX M] (α : Type) (β : Type) where
  guard (m : M) (x : α) : Prop := True
  action (m : M) (x : α) (grd : guard m x): (β × M)

theorem _Guard_ext [Machine CTX M] (guard₁ : M → α → Prop) (guard₂ : M → α → Prop):
  (∀ m x, guard₁ m x = guard₂ m x)
  → guard₁ = guard₂ :=
by
  intro H
  funext m x
  exact H m x

theorem _Guard_coext [Machine CTX M] (guard₁ : M → α → Prop) (guard₂ : M → α → Prop):
  guard₁ = guard₂
  → ∀ m x, guard₁ m x = guard₂ m x
 :=
by
  intro H
  intros m x
  exact congrFun (congrFun H m) x

/- XXX : does this axiom breaks something ?
         (I don't think it's provable because of HEq) -/
axiom _Action_ext_ax {CTX} {M} [Machine CTX M] {α β} (ev₁ ev₂: Event M α β):
   (∀ m x, ev₁.guard m x = ev₂.guard m x
          ∧ ∀ grd₁ grd₂, ev₁.action m x grd₁ = ev₂.action m x grd₂)
   → HEq ev₁.action ev₂.action

theorem Event.ext' {CTX} {M} [Machine CTX M] {α β} (ev₁ ev₂: Event M α β):
  (∀ m x, ev₁.guard m x = ev₂.guard m x
          ∧ ∀ grd₁ grd₂, ev₁.action m x grd₁ = ev₂.action m x grd₂)
  → ev₁ = ev₂ :=
by
  intros H
  have Hax := _Action_ext_ax ev₁ ev₂
  cases ev₁
  case mk g₁ act₁=>
    cases ev₂
    case mk g₂ act₂ =>
      simp at*
      constructor
      case left =>
        apply _Guard_ext
        intros m x
        have Hg := (H m x).1
        exact propext Hg
      case right =>
        exact Hax H



/-- The internal representation of all *deterministic* initialization events
with: `M` the machine type,
`α` the input type, and `β` the output type of the event
.-/
@[ext]
structure InitEvent (M) [Machine CTX M] (α) (β : Type) where
  guard (x : α) : Prop := True
  init (x : α) (grd : guard x) : (β × M)

@[simp]
def InitEvent.toEvent [DecidableEq M] [Inhabited M] [Machine CTX M] (ev : InitEvent M α β) : Event M α β :=
  {
    guard := fun m x => m == default ∧ ev.guard x
    action := fun m x grd => ev.init x (by simp at grd ; apply grd.2)

  }

/-- The deterministic skip event, that does nothing.
Note that the output type must match the input type,
 hence a non-deterministic notion of skip event is
 best in most situations (cf. `_NDEvent` in the `NonDet` module). -/
@[simp]
def skip_Event (M) [Machine CTX M] (α) : Event M α α :=
{
  action := fun m x _ => (x, m)
}

/-- Any type-theoretic function can be lifted to the
status of a (non-guarded) event. -/
@[simp]
def fun_Event  (M) [Machine CTX M] (f : α → β) : Event M α β :=
{
  action := fun m x _ => (f x, m)

}

/-- This allows to lift a "stateful" function. -/
@[simp]
def funskip_Event (M) [Machine CTX M] (xf : M → α → β) : Event M α β :=
{
  action := fun m x _ => (xf m x, m)

}
