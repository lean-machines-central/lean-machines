import LeanMachines.Event.Prelude
import LeanMachines.Algebra.Contravariant
import LeanMachines.Algebra.Profunctor
import LeanMachines.Algebra.Arrow

/-!

# Basic definitions

This module contains the basic definitions of the LeanMachines
framework:

 - Machine types, instances of the `Machine` typeclass
 - Events, elements of the type `_Event`.

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

class Machine (CTX : outParam (Type u)) (M)
  extends Inhabited M where
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
structure _Event (M) [Machine CTX M] (α : Type) (β : Type) where
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
axiom _Action_ext_ax {CTX} {M} [Machine CTX M] {α β} (ev₁ ev₂: _Event M α β):
   (∀ m x, ev₁.guard m x = ev₂.guard m x
          ∧ ∀ grd₁ grd₂, ev₁.action m x grd₁ = ev₂.action m x grd₂)
   → HEq ev₁.action ev₂.action

theorem _Event.ext' {CTX} {M} [Machine CTX M] {α β} (ev₁ ev₂: _Event M α β):
  (∀ m x, ev₁.guard m x = ev₂.guard m x
          ∧ ∀ grd₁ grd₂, ev₁.action m x grd₁ = ev₂.action m x grd₂)
  → ev₁ = ev₂ :=
by
  intros H
  have Hax := _Action_ext_ax ev₁ ev₂
  cases ev₁
  case mk g₁ act₁ =>
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
structure _InitEvent (M) [Machine CTX M] (α) (β : Type) where
  guard (x : α) : Prop := True
  init (x : α) (grd : guard x) : (β × M)

@[simp]
def _InitEvent.to_Event [DecidableEq M] [Machine CTX M] (ev : _InitEvent M α β) : _Event M α β :=
  {
    guard := fun m x => m == default ∧ ev.guard x
    action := fun m x grd => ev.init x (by simp at grd ; apply grd.2)
  }

/-- The deterministic skip event, that does nothing.
Note that the output type must match the input type,
 hence a non-deterministic notion of skip event is
 best in most situations (cf. `_NDEvent` in the `NonDet` module). -/
@[simp]
def skip_Event (M) [Machine CTX M] (α) : _Event M α α :=
{
  action := fun m x _ => (x, m)
}

/-- Any type-theoretic function can be lifted to the
status of a (non-guarded) event. -/
@[simp]
def fun_Event  (M) [Machine CTX M] (f : α → β) : _Event M α β :=
{
  action := fun m x _ => (f x, m)
}

/-- This allows to lift a "stateful" function. -/
@[simp]
def funskip_Event (M) [Machine CTX M] (xf : M → α → β) : _Event M α β :=
{
  action := fun m x _ => (xf m x, m)
}

/-!
## Algebraic properties of events

The following instantiate various algebraic structures
for the representation type of deterministic events: `_Event`.

This part is rather experimental and is thus not fully documented yet.

-/


/- Functor -/

def map_Event [Machine CTX M] (f : α → β) (ev : _Event M γ α)  : _Event M γ β :=
  { guard := ev.guard
    action := fun m x grd => let (y, m') := (ev.action m x grd)
                             (f y, m')
   }

instance [Machine CTX M]: Functor (_Event M γ) where
  map := map_Event

instance [Machine CTX M]: LawfulFunctor (_Event M γ) where
  map_const := by
    intros α β
    simp [Functor.mapConst, Functor.map]
  id_map := by
    intros α ev
    simp [Functor.map, map_Event]
  comp_map := by
    intros α _ γ g h x
    simp [Functor.map, map_Event]

/- Applicative Functor -/

@[simp]
def pure_Event [Machine CTX M] (y : α) : _Event M γ α :=
  {
    action := fun m _ _ => (y, m)
  }

instance [Machine CTX M]: Pure (_Event M γ) where
  pure := pure_Event

def apply_Event [Machine CTX M] ( ef : _Event M γ (α → β)) (ev : _Event M γ α) : _Event M γ β :=
  {
    guard := fun m x => ef.guard m x ∧ ((efg : ef.guard m x)
                                         →  ev.guard (ef.action m x efg).snd x)
    action := fun m x grd => let (y, m'') := ev.action (ef.action m x grd.1).2 x (grd.2 grd.1)
                             ((ef.action m x grd.1).1 y, m'')
  }

instance [Machine CTX M]: Applicative (_Event M γ) where
  seq ef ev := apply_Event ef (ev ())

theorem Pure_seq_aux [Machine CTX M] (g : α → β) (ev : _Event M γ α):
  apply_Event (pure g) ev = map_Event g ev :=
by
  apply _Event.ext'
  intros m x
  simp [apply_Event, pure, map_Event]


instance [Machine CTX M]: LawfulApplicative (_Event M γ) where
  map_const := by intros ; rfl
  id_map := by intros ; rfl
  seqLeft_eq := by intros ; rfl
  seqRight_eq := by intros ; rfl
  pure_seq := by
    intros α β g ev
    simp [pure, Seq.seq, Functor.map]
    apply Pure_seq_aux

  map_pure := by intros α β g x ; rfl
  seq_pure := by
    intros α β ev x
    simp [Seq.seq, Functor.map, pure]
    apply _Event.ext'
    simp [apply_Event, map_Event]

  seq_assoc := by
    intros α β γ' ev g h
    simp [Functor.map, Seq.seq]
    apply _Event.ext
    case guard =>
      simp [apply_Event, map_Event]
      funext m x
      refine propext ?_
      constructor <;> intro H <;> simp [H]
    case action =>
      apply _Action_ext_ax
      intros m x
      simp [apply_Event, map_Event]
      constructor <;> intro H <;> simp [H]

/- Monad -/

def bind_Event [Machine CTX M] (ev : _Event M γ α) (f : α → _Event M γ β) : _Event M γ β :=
  {
    guard := fun m x => ev.guard m x ∧
                        ((grd : ev.guard m x) →
                          (f (ev.action m x grd).1).guard (ev.action m x grd).2 x)

    action := fun m x grd =>
      (f (ev.action m x grd.1).1).action (ev.action m x grd.1).2 x (grd.2 grd.1)

  }


instance [Machine CTX M]: Monad (_Event M γ) where
  bind := bind_Event

instance [Machine CTX M]: LawfulMonad (_Event M γ) where
  bind_pure_comp := by
    intros α β f ev
    simp [pure, Functor.map, bind]
    apply _Event.ext'
    intros m x
    simp [bind_Event, map_Event]

  bind_map := by simp [bind] ; intros ; rfl

  pure_bind := by
    intros α β x f
    simp [pure, bind]
    apply _Event.ext'
    intros m y
    simp [bind_Event]

  bind_assoc := by
    intros β γ' x f g h
    simp [bind]
    apply _Event.ext
    case guard =>
      funext m x
      simp [bind_Event]
      constructor <;> intro H <;> simp [H]
    case action =>
      apply _Action_ext_ax
      intros m x
      simp [bind_Event]
      constructor <;> intro H <;> simp [H]

/- arrows -/

abbrev _KEvent M [Machine CTX M] γ := Kleisli (_Event M γ)
  -- α → (_Event M γ) β

--def instArrowKEvent [Machine CTX M]: Arrow (_KEvent M γ) := inferInstance

/-
variable (f : α → β)
variable (M)
variable (instM : Machine CTX M)
variable (γ)
#check (Arrow.arrow f : _KEvent M γ α β)
-/

-- Arrows are in a way less powerful (but more general) than Monads
-- but Events are monads only considering their output type
-- while arrows apply to both input and output types

instance [Machine CTX M]: Category (_Event M) where
  id := fun_Event M id

  comp {α β γ} (ev₂ : _Event M β γ) (ev₁ : _Event M α β) : _Event M α γ :=
    { guard := fun m x => ev₁.guard m x ∧
                          ((grd : ev₁.guard m x) →  let (y, m') := ev₁.action m x grd
                                          ev₂.guard m' y)
      action := fun m x grd => ev₂.action (ev₁.action m x grd.1).2 (ev₁.action m x grd.1).1 (grd.2 grd.1)
    }

instance [Machine CTX M]: LawfulCategory (_Event M) where
  id_right ev := by
    apply _Event.ext
    case guard => simp
    case action => apply _Action_ext_ax ; intros ; simp

  id_left ev := by
    apply _Event.ext
    case guard => simp
    case action => apply _Action_ext_ax ; intros ; simp

  id_assoc ev₁ ev₂ ev₃ := by
    apply _Event.ext
    case guard =>
      simp
      funext m x
      simp
      constructor <;> intro H <;> simp [H]
    case action =>
      apply _Action_ext_ax
      intros m x
      simp
      constructor <;> intro H <;> simp [H]

@[simp]
def _Event_Arrow_first [Machine CTX M] (ev : _Event M α β) : _Event M (α × γ) (β × γ) :=
  { guard := fun m (x, _) => ev.guard m x
    action := fun m (x, y) grd => let (x', m') := ev.action m x grd
                              ((x',y), m')
  }

/- one possible definition
instance [Machine CTX M]: Arrow (_Event M) where
  arrow {α β} (f : α → β) := fun_Event M f

  split {α α' β β'} (ev₁ : _Event M α β)  (ev₂ : _Event M α' β') : _Event M (α × α') (β × β') :=
    Arrow.split_from_first (fun_Event M (fun (x, y) => (y, x)))
                           _Event_Arrow_first
                           ev₁ ev₂
-/

-- more explicit alternative

instance [Machine CTX M]: Arrow (_Event M) where
  arrow {α β} (f : α → β) := {
    guard := fun _ _ => True
    action := fun m x _ => (f x, m)
  }

  split {α α' β β'} (ev₁ : _Event M α β)  (ev₂ : _Event M α' β') : _Event M (α × α') (β × β') := {
    guard := fun m (x, y) => ev₁.guard m x ∧ ev₂.guard m y
    action := fun m (x, y) grd => let (x',m') := ev₁.action m x grd.1
                              let (y', _) := ev₂.action m y grd.2
                              -- note : we forget the second state change
                              ((x', y'), m')
  }



instance [Machine CTX M]: LawfulArrow (_Event M) where
  arrow_id := by simp [Arrow.arrow]
  arrow_ext _ := by
    apply _Event.ext'
    simp [Arrow.arrow, Arrow.first]
  arrow_fun _ _ := by
    apply _Event.ext'
    simp [Arrow.arrow, Arrow.first]
  arrow_xcg _ _ := by
    apply _Event.ext'
    simp [Arrow.arrow, Arrow.first]
  arrow_unit _ := by
    apply _Event.ext'
    simp [Arrow.arrow, Arrow.first]
  arrow_assoc {α β γ δ} (f : _Event M α β) := by
    apply _Event.ext'
    simp [Arrow.arrow, Arrow.first]

/-  ArrowChoice -/

def altEvent [Machine CTX M] (evl : _Event M α β) (evr : _Event M γ δ)
  : _Event M (Sum α γ) (Sum β δ) :=
  {
    guard := fun m x => match x with
                        | .inl l => evl.guard m l
                        | .inr r => evr.guard m r
    action := fun m x grd => match x with
                        | .inl l => let (y, m') := evl.action m l grd
                                    (Sum.inl y, m')
                        | .inr r => let (y, m') := evr.action m r grd
                                    (Sum.inr y, m')
  }

instance [Machine CTX M]: ArrowChoice (_Event M) where
  splitIn := altEvent


/- ContravariantFunctor functor -/

abbrev _CoEvent (M) [Machine CTX M] (α) (β) :=
  _Event M β α

@[simp]
def coEvent_from_Event [Machine CTX M] (ev : _Event M α β) : _CoEvent M β α :=
 ev

@[simp]
def Event_from_CoEvent [Machine CTX M] (ev : _CoEvent M β α) : _Event M α β :=
 ev

instance [Machine CTX M] : ContravariantFunctor (_CoEvent M γ) where
  contramap f ev := {
    guard := fun m x => ev.guard m (f x)
    action := fun m x => ev.action m (f x)
  }

instance [Machine CTX M] : LawfullContravariantFunctor (_CoEvent M β) where
  cmap_id _ := rfl
  cmap_comp _ _ := rfl

/- Profunctor -/

-- An indirect definition using the covariant and contravariant functors
--instance [Machine CTX M] : Profunctor (_Event M) where
--  dimap {α β} {γ δ} (f : β → α) (g : γ → δ) (ev : _Event M α γ) : _Event M β δ :=
--    let ev' := Event_from_CoEvent (ContravariantFunctor.contramap f (coEvent_from_Event ev))
--    Functor.map g ev'

-- alternatively, a direct definition
instance [Machine CTX M] : Profunctor (_Event M) where
  dimap {α β} {γ δ} (f : β → α) (g : γ → δ) (ev : _Event M α γ) : _Event M β δ :=
  { guard m x := ev.guard m (f x)
    action m x grd := let (y, m') := ev.action m (f x) grd
                      (g y, m')
  }

instance [Machine CTX M] : LawfulProfunctor (_Event M) where
  dimap_id := rfl
  dimap_comp _ _ _ _ := rfl

instance [Machine CTX M] : StrongProfunctor (_Event M) where
  first' {α β γ} (ev : _Event M α β): _Event M (α × γ) (β × γ) :=
    {
      guard := fun m (x, _) => ev.guard m x
      action := fun m (x, y) grd => let (x', m') := ev.action m x grd
                                    ((x', y), m')
    }

instance [Machine CTX M] : LawfulStrongProfunctor (_Event M) where
