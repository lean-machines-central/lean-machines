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

 - a `reset` state, that defines the (unique) state of the machine before
 its initialization (very often, this is the default initialization state,
  but it can also be an unreachable "pre-init" state if required).

Note : the machine state (type M) is assumed to have decidable equality
 because states must be at times compared  (e.g. tracking the `reset` state).
 For this reason the `invariant` is a separate component.

-/

class Machine (CTX : outParam Type) (M : Type) [DecidableEq M] where
  /-- The context (i.e. parameters) of the machine. -/
  context : CTX
  /-- The invariant property that must be satisfied
  by a machine (state) of type `M`. -/
  invariant : M → Prop
  /-- The "before initialization", or *reset state*. -/
  reset : M

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
structure _Event (M) [DecidableEq M] [Machine CTX M] (α : Type) (β : Type) where
  /-- Boolean guard of the action -/
  guard : M → α → Bool := fun _ _ => true
  /-- Internal representation of the event action as a function -/
  action (m : M) (x : α): Option (β × M)

 -- Note : the Option is because internally there is no way to
 --        make the internal action depending on the validity of the guard

/-- The internal representation of all *deterministic* initialization events
with: `M` the machine type,
`α` the input type, and `β` the output type of the event
-/

@[ext]
structure _InitEvent (M) [DecidableEq M] [Machine CTX M] (α) (β : Type) where
  guard : α → Bool
  init: α → Option (β × M)

@[simp]
def _InitEvent.to_Event [DecidableEq M] [Machine CTX M] (ev : _InitEvent M α β) : _Event M α β :=
  {
    guard := fun m x => m == Machine.reset && ev.guard x
    action := fun _ x => ev.init x
  }

/-- The deterministic skip event, that does nothing.
Note that the output type must match the input type,
 hence a non-deterministic notion of skip event is
 best in most situations (cf. `_NDEvent` in the `NonDet` module). -/
@[simp]
def skip_Event (M) [DecidableEq M] [Machine CTX M] (α) : _Event M α α :=
{
  action := fun m x => some (x, m)
}

/-- Any type-theoretic function can be lifted to the
status of a (non-guarded) event. -/
@[simp]
def fun_Event (M) [DecidableEq M] [Machine CTX M] (f : α → β) : _Event M α β :=
{
  action := fun m x => some (f x, m)
}

/-- This allows to lift a "stateful" function. -/
@[simp]
def funskip_Event (M) [DecidableEq M] [Machine CTX M] (xf : M → α → β) : _Event M α β :=
{
  action := fun m x => some (xf m x, m)
}

/-!
## Algebraic properties of events

The following instantiate various algebraic structures
for the representation type of deterministic events: `_Event`.

This part is rather experimental and is thus not fully documented yet.

-/


/- Functor -/

def map_Event [DecidableEq M] [Machine CTX M] (f : α → β) (ev : _Event M γ α)  : _Event M γ β :=
  { guard := ev.guard
    action := fun m x => match ev.action m x with
                         | .none => .none
                         | .some (y, m') => .some (f y, m')
   }

instance [DecidableEq M] [Machine CTX M]: Functor (_Event M γ) where
  map := map_Event

instance [DecidableEq M] [Machine CTX M]: LawfulFunctor (_Event M γ) where
  map_const := by
    intros α β
    simp [Functor.mapConst, Functor.map]
  id_map := by
    intros α ev
    simp [Functor.map, map_Event]
    cases ev
    case mk evr act =>
      simp
      funext m x
      cases (act m x) <;> simp
  comp_map := by
    intros α _ γ g h ev
    simp [Functor.map, map_Event]
    funext m x
    split <;> rfl

/- Applicative Functor -/

@[simp]
def pure_Event [DecidableEq M] [Machine CTX M] (y : α) : _Event M γ α :=
  {
    action := fun m _ => (y, m)
  }

instance [DecidableEq M] [Machine CTX M]: Pure (_Event M γ) where
  pure := pure_Event

def apply_Event [DecidableEq M] [Machine CTX M] ( ef : _Event M γ (α → β)) (ev : _Event M γ α) : _Event M γ β :=
  {
    guard := fun m x => ef.guard m x && match ef.action m x with
                                       | .none => true
                                       | .some (_, m') => ev.guard m' x
    action := fun m x =>
      match ef.action m x with
      |.none => .none
      | .some (f, m') => match ev.action m' x with
                         | .none => none
                         | .some (y, m'') => some (f y, m'')
  }

instance [DecidableEq M] [Machine CTX M]: Applicative (_Event M γ) where
  seq ef ev := apply_Event ef (ev ())

instance [DecidableEq M] [Machine CTX M]: LawfulApplicative (_Event M γ) where
  map_const := by intros ; rfl
  id_map := by intros ; simp
  seqLeft_eq := by intros ; rfl
  seqRight_eq := by intros ; rfl
  pure_seq := by
    intros α β g x
    simp [Seq.seq, Functor.map, map_Event, pure, pure_Event, apply_Event]
  map_pure := by intros α β g x ; rfl
  seq_pure := by
    intros α β ev x
    simp [Seq.seq, pure, Functor.map, map_Event, apply_Event]
    constructor <;> (funext m y ; cases ev.action m y <;> simp)

  seq_assoc := by
    intros α β γ' ev g h
    simp [Seq.seq, Functor.map, map_Event, apply_Event]
    constructor
    case left =>
      funext m y
      cases h.action m y
      · simp
      · simp
        rename_i res
        cases g.action res.snd y
        · simp
        case _ res' =>
          simp
          exact Eq.symm (Bool.and_assoc (h.guard m y) (g.guard res.snd y) (ev.guard res'.snd y))
    case right => -- XXX: some redundancy here ...
      funext m y
      cases h.action m y
      · simp
      case _ res =>
        simp
        cases g.action res.snd y
        · simp
        case _ res' =>
          simp
          cases ev.action res'.snd y <;> simp


/- Monads -/

def bind_Event [Machine CTX M] (ev : _Event M γ α) (f : α → _Event M γ β) : _Event M γ β :=
  {
    guard := fun m x => ev.guard m x ∧ match ev.action m x with
                                       | .none => True
                                       | .some (y, m') =>
                                           let ev' := f y
                                           ev'.guard m' x
    action := fun m x => match ev.action m x with
                         | .none => none
                         | .some (y, m') =>
                             let ev' := f y
                             ev'.action m' x
  }

instance [Machine CTX M]: Monad (_Event M γ) where
  bind := bind_Event

instance [Machine CTX M]: LawfulMonad (_Event M γ) where
  bind_pure_comp := by
    intros α β f ev
    simp [pure, Functor.map, pure_Event, map_Event, bind, bind_Event]
    funext m x
    cases ev.action m x <;> simp
  bind_map := by
    intros α β evf ev
    simp [bind, Seq.seq, Functor.map, bind_Event, map_Event, apply_Event]
    constructor <;> (funext m x <;> cases evf.action m x <;> simp)
  pure_bind := by intros _ β x f
                  simp [pure, bind, bind_Event]
  bind_assoc := by
    intros β γ' x f g h
    simp [bind, bind_Event]
    constructor
    case left =>
      funext m x
      cases f.action m x
      · simp
      case _ res =>
        simp
        cases (g res.fst).action res.snd x
        · simp
        case _ res' =>
          simp
          exact and_assoc
    case right =>
      funext m x
      cases f.action m x <;> simp

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

-- Arrows are less powerful (but more general) than Monads
-- but Events are monads in their output type
-- and both monads and arrows do not apply on input types

instance [Machine CTX M]: Category (_Event M) where
  id := fun_Event M id

  comp {α β γ} (ev₂ : _Event M β γ) (ev₁ : _Event M α β) : _Event M α γ :=
    { guard := fun m x => ev₁.guard m x ∧ match ev₁.action m x with
                                          | .none => True
                                          | .some (y, m') => ev₂.guard m' y
      action := fun m x => match ev₁.action m x with
                                          | .none => none
                                          | .some (y, m') => ev₂.action m' y
    }

instance [Machine CTX M]: LawfulCategory (_Event M) where
  id_right _ := by simp
  id_left ev := by
    cases ev
    case mk evr act =>
      simp
      constructor
      case left =>
        cases evr
        case mk grd =>
          simp
          funext m x
          cases act m x <;> simp
      case right =>
        funext m x
        cases act m x <;> simp

  id_assoc ev₁ ev₂ ev₃ := by
    cases ev₁
    case mk evr₁ act₁ =>
      cases ev₂
      case mk evr₂ act₂ =>
        cases ev₃
        case mk evr₃ act₃ =>
          simp
          constructor
          case left =>
            funext m x
            cases act₃ m x
            · simp
            case _ res₃ =>
              simp
              cases act₂ res₃.snd res₃.fst
              · simp
              case _ res₂ =>
                simp
                exact and_assoc
          case right =>
            funext m x
            cases act₃ m x <;> simp


/- one possible definition : split from first  (an old version with non-optional actions)

@[simp]
def _Event_Arrow_first [Machine CTX M] (ev : _Event M α β) : _Event M (α × γ) (β × γ) :=
  { guard := fun m (x, _) => ev.guard m x
    action := fun m (x, y) => let (x', m') := ev.action m x
                              ((x',y), m')
  }

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
    action := fun m x => (f x, m)
  }

  split {α α' β β'} (ev₁ : _Event M α β)  (ev₂ : _Event M α' β') : _Event M (α × α') (β × β') := {
    guard := fun m (x, y) => ev₁.guard m x ∧ ev₂.guard m y
    action := fun m (x, y) =>
      match ev₁.action m x with
      | .none => none
      | .some (x',m') =>
           match ev₂.action m y with
           | .none => none
           | .some (y', _) =>
                -- note : we forget the second state change, like in the split-from-first case
                -- implicitly this means that the state changes should be "compatibl"
                -- a more interesting variant is possible with non-deterministic events
                some ((x', y'), m')
  }

instance [Machine CTX M]: LawfulArrow (_Event M) where
  arrow_id := by simp [Arrow.arrow]
  arrow_ext _ := by simp [Arrow.arrow, Arrow.first]
  arrow_fun _ _ := by simp [Arrow.arrow, Arrow.first]
  arrow_xcg ev f := by
    simp [Arrow.arrow, Arrow.first]
    constructor <;> funext m (x, y) <;> cases ev.action m x <;> simp
  arrow_unit ev := by
    simp [Arrow.arrow, Arrow.first]
    constructor <;> funext m (x, y) <;> cases ev.action m x <;> simp
  arrow_assoc {α β γ δ} (f : _Event M α β) := by
    simp [Arrow.arrow, Arrow.first]
    constructor <;> funext m ((x, y), z) <;> cases f.action m x <;> simp


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

instance [Machine CTX M] : Profunctor (_Event M) where
  dimap {α β} {γ δ} (f : β → α) (g : γ → δ) (ev : _Event M α γ) : _Event M β δ :=
    let ev' := Event_from_CoEvent (ContravariantFunctor.contramap f (coEvent_from_Event ev))
    Functor.map g ev'

instance [Machine CTX M] : LawfulProfunctor (_Event M) where
  dimap_id {α β} := by
    simp [Profunctor.dimap, ContravariantFunctor.contramap]
    funext ev
    simp

  dimap_comp f1 f2 f3 f4 := by
    simp [Profunctor.dimap]
    funext ev
    simp
    cases ev
    case mk evr act =>
      simp [Functor.map, map_Event, ContravariantFunctor.contramap]
      funext m x
      cases act m (f2 (f1 x)) <;> simp

instance [Machine CTX M] : StrongProfunctor (_Event M) where
  first' {α β γ} (ev : _Event M α β): _Event M (α × γ) (β × γ) :=
    {
      guard := fun m (x, _) => ev.guard m x
      action := fun m (x, y) => match ev.action m x with
                                | .none => none
                                | .some (x', m') => some ((x', y), m')
    }

instance [Machine CTX M] : LawfulStrongProfunctor (_Event M) where


/-  Other combinators -/


open Either

def altEvent [Machine CTX M] (evl : _Event M α α') (evr : _Event M β β')
  : _Event M (Either α β) (Either α' β') :=
  {
    guard := fun m x => match x with
                        | left l => evl.guard m l
                        | right r => evr.guard m r
    action := fun m x => match x with
                        | left l => match evl.action m l with
                                    | .none => none
                                    | .some (y, m') => some (left y, m')
                        | right r => match evr.action m r with
                                     | .none => .none
                                     | .some (y, m') => some (right y, m')
  }
