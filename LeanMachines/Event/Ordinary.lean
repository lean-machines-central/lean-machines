
import LeanMachines.Event.Prelude
import LeanMachines.Event.Basic
import LeanMachines.Algebra.Contravariant
import LeanMachines.Algebra.Profunctor
import LeanMachines.Algebra.Arrow

/-!
# Ordinary Deterministic events

This module defines the user-level API for constructing
and manipulating **ordinary deterministic** events.

In LeanMachines, an event is said **ordinary** if it
is not demonstrated anticipated or convergent
(cf. `Event.Convergent` module).

-/

/-- The internal representation of proof obligations for ordinary
deterministic events. -/
structure _EventPO [Machine CTX M] (ev : _Event M α β) (kind : EventKind) where
  safety (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → Machine.invariant (ev.action m x).snd

/-- The type of deterministic events without convergence properties.
It is an event for machine type `M` with input type `α` and output type `β` -/
structure OrdinaryEvent (M) [Machine CTX M] (α) (β) extends _Event M α β where
  po : _EventPO to_Event  (EventKind.TransDet Convergence.Ordinary)

/-- The specification of a deterministic, ordinary event for machine `M`
with input type `α` and output type `β`. . -/
structure EventSpec (M) [Machine CTX M] (α) (β) where
  /-- The guard property of the event, in machine state `m` with input `x`. -/
  guard (m : M) (x : α) : Prop := True
  /-- The (deterministic) action of the event, with
      previous machine state `m` and input `x`, building a pair
      `(y, m')` with `y` an output value and `m'` the next machine state.

      **Remark: the guard property is supposed valid any time the action
      is to be performed in proof obligations. However, this is not captured
      at the type level (a type-level guard-dependent variant is currently being
      investigated). -/
  action (m : M) (x : α) : β × M

  /-- The safety proof obligation. -/
  safety (m : M) (x : α) :
    Machine.invariant m
    → guard m x
    → Machine.invariant (action m x).2

@[simp]
def _Event.toEventSpec [Machine CTX M]
  (ev : _Event M α β)
  (Hsafe : (m : M) → (x : α) →  Machine.invariant m
                           → ev.guard m x
                           → Machine.invariant (ev.action m x).snd) : EventSpec M α β :=
  { guard := ev.guard
    action := ev.action
    safety := Hsafe
  }

@[simp]
def EventSpec.to_Event [Machine CTX M] (ev : EventSpec M α β) : _Event M α β :=
  { guard := ev.guard
    action := ev.action
  }

/-- Construction of an ordinary deterministic event from a
`EventSpec` specification. -/
@[simp]
def newEvent {M} [Machine CTX M] (ev : EventSpec M α β) : OrdinaryEvent M α β :=
  { to_Event := ev.to_Event
    po := {
      safety := fun m x => by
        simp
        intros Hinv Hgrd
        apply ev.safety <;> assumption
    }
  }

/-- Variant of `EventSpec` with implicit `Unit` output type -/
structure EventSpec' (M) [Machine CTX M] (α) where
  guard (m : M) (x : α) : Prop := True
  action (m : M) (x : α) : M
  safety (m : M) (x : α) :
    Machine.invariant m
    → guard m x
    → Machine.invariant (action m x)

@[simp]
def EventSpec'.toEventSpec [Machine CTX M] (ev : EventSpec' M α) : EventSpec M α Unit :=
  {
    guard := ev.guard
    action := fun m x => ((), ev.action m x)
    safety := fun m x => by simp ; apply ev.safety
  }

/-- Variant of `newEvent` with implicit `Unit` output type -/
@[simp]
def newEvent' {M} [Machine CTX M] (ev : EventSpec' M α) : OrdinaryEvent M α Unit :=
  newEvent ev.toEventSpec

/-- Variant of `EventSpec` with implicit `Unit` input and output types -/
structure EventSpec'' (M) [Machine CTX M] where
  guard (m : M) : Prop := True
  action (m : M) : M
  safety (m : M) :
    Machine.invariant m
    → guard m
    → Machine.invariant (action m)

@[simp]
def EventSpec''.toEventSpec [Machine CTX M] (ev : EventSpec'' M) : EventSpec M Unit Unit :=
  {
    guard := fun m () => ev.guard m
    action := fun m () => ((), ev.action m)
    safety := fun m () => by simp ; apply ev.safety
  }

/-- Variant of `newEvent` with implicit `Unit` input and output types -/
@[simp]
def newEvent'' {M} [Machine CTX M] (ev : EventSpec'' M) : OrdinaryEvent M Unit Unit :=
  newEvent ev.toEventSpec

def skipEvent (M) [Machine CTX M] (α) : OrdinaryEvent M α α :=
  newEvent ((skip_Event M α).toEventSpec
                                 (by intros ; simp [skip_Event] ; assumption))

/-!

## Initialization events (deterministic)

Initialization events, of the deterministic kind,
are ordinary deterministic events with the *reset* state as a pre-state.

 -/

/-- The internal representation of proof obligations for initialization events. -/
structure _InitEventPO [Machine CTX M] (ev : _InitEvent M α β) (kind : EventKind) where
  safety (x : α):
    ev.guard x
    → Machine.invariant (ev.init x).snd


/-- Type type of deterministic initialization events.
It is an event for machine type `M` with input type `α` and output type `β` -/
structure InitEvent (M) [Machine CTX M] (α) (β) extends _InitEvent M α β where
  po : _InitEventPO to_InitEvent EventKind.InitDet

/-- The specification of a deterministic ordinary event for machine `M`
with input type `α` and output type `β`. . -/
structure InitEventSpec (M) [Machine CTX M] (α) (β) where
  /-- The guard property of the event, an initialization with input `x`. -/
  guard (x : α) : Prop := True
  /-- The (deterministic) action of the event, with input `x`, building a pair
      `(y, m)` with `y` an output value and `m` an initial machine state.-/
  init (x : α) : β × M
  /-- The safety proof obligation. -/
  safety (x : α) :
    guard x
    → Machine.invariant (init x).2

@[simp]
def InitEventSpec.to_InitEvent [Machine CTX M] (ev : InitEventSpec M α β) : _InitEvent M α β :=
  {
    guard := ev.guard
    init := ev.init
  }

/-- Construction of a deterministic initialization event from a
`InitEventSpec` specification. -/
@[simp]
def newInitEvent {M} [Machine CTX M] (ev : InitEventSpec M α β) : InitEvent M α β :=
  {
    to_InitEvent := ev.to_InitEvent
    po := {
      safety := fun x => by simp
                            intro Hgrd
                            apply ev.safety x Hgrd

    }
  }

/-- Variant of `InitEventSpec` with implicit `Unit` output type -/
structure InitEventSpec' (M) [Machine CTX M] (α) where
  guard (x : α) : Prop := True
  init (x : α) : M
  safety (x : α) :
    guard x
    → Machine.invariant (init x)

@[simp]
def InitEventSpec'.toInitEventSpec [Machine CTX M] (ev : InitEventSpec' M α) : InitEventSpec M α Unit :=
  {
    guard := ev.guard
    init := fun x => ((), ev.init x)
    safety := fun x => by simp ; apply ev.safety
  }

/-- Variant of `newInitEvent` with implicit `Unit` output type -/
@[simp]
def newInitEvent' {M} [Machine CTX M] (ev : InitEventSpec' M α) : InitEvent M α Unit :=
  newInitEvent ev.toInitEventSpec

/-- Variant of `InitEventSpec` with implicit `Unit` input and output types -/
structure InitEventSpec'' (M) [Machine CTX M] where
  guard : Prop := True
  init : M
  safety :
    guard
    → Machine.invariant init

@[simp]
def InitEventSpec''.toInitEventSpec [Machine CTX M] (ev : InitEventSpec'' M) : InitEventSpec M Unit Unit :=
  {
    guard := fun () => ev.guard
    init := fun () => ((), ev.init)
    safety := fun () => by simp ; apply ev.safety
  }

/-- Variant of `newInitEvent` with implicit `Unit` input and output types -/
@[simp]
def newInitEvent'' {M} [Machine CTX M] (ev : InitEventSpec'' M) : InitEvent M Unit Unit :=
  newInitEvent ev.toInitEventSpec

/-!
## Algebraic properties of events

The following instantiate various algebraic structures, complementing
the structural properties of the representation types (`_Event`) with
more "lawful" properties for the main event type (`OrdinaryEvent`).

This part is rather experimental and is thus not fully documented yet.

-/

/- Functor -/

@[simp]
def funEvent (M) [Machine CTX M] (f : α → β) : OrdinaryEvent M α β :=
  newEvent ((fun_Event M f).toEventSpec
                                 (fun m x Hinv _ => by simp [fun_Event] ; assumption))

def mapEvent [Machine CTX M] (f : α → β) (ev : OrdinaryEvent M γ α) : OrdinaryEvent M γ β :=
  {
    to_Event := Functor.map f ev.to_Event
    po := { safety := fun m x => by intros Hinv Hgrd
                                    simp [Functor.map, map_Event] at *
                                    apply ev.po.safety m x Hinv Hgrd
  }
}

instance [Machine CTX M] : Functor (OrdinaryEvent M γ) where
  map := mapEvent

instance [Machine CTX M] : LawfulFunctor (OrdinaryEvent M γ) where
  map_const := rfl
  id_map := by intros ; rfl
  comp_map := by intros ; rfl

/- Applicative Functor -/

@[simp]
def pureEvent [Machine CTX M] (y : α) : OrdinaryEvent M γ α :=
  {
    to_Event := pure y
    po := {
      safety := fun m _ => by simp [pure]
    }
  }

instance [Machine CTX M]: Pure (OrdinaryEvent M γ) where
  pure := pureEvent

def applyEvent [Machine CTX M] ( ef : OrdinaryEvent M γ (α → β)) (ev : OrdinaryEvent M γ α) : OrdinaryEvent M γ β :=
  let event := ef.to_Event <*> ev.to_Event
  {
    guard := event.guard
    action := event.action
    po := {
      safety := fun m x => by simp [event, Seq.seq, apply_Event]
                              intros Hinv Hgrd₁ Hgrd₂
                              have Hsafe₁ := ef.po.safety m x Hinv Hgrd₁
                              apply ev.po.safety (ef.to_Event.action m x).snd
                              <;> assumption
    }
  }

instance [Machine CTX M]: Applicative (OrdinaryEvent M γ) where
  seq ef ev := applyEvent ef (ev ())

instance [Machine CTX M]: LawfulApplicative (OrdinaryEvent M γ) where
  map_const := by intros ; rfl
  id_map := by intros ; rfl
  seqLeft_eq := by intros ; rfl
  seqRight_eq := by intros ; rfl
  pure_seq := by intros α β g ev
                 cases ev
                 case mk ev po =>
                   simp [Seq.seq, applyEvent, pure, pureEvent, Functor.map, mapEvent, apply_Event, map_Event]

  map_pure := by intros α β g x ; rfl
  seq_pure := by intros α β ev x
                 simp [Seq.seq, pure, Functor.map, applyEvent, apply_Event, mapEvent, map_Event]

  seq_assoc := by intros α β γ' ev g h
                  simp [Seq.seq, Functor.map, mapEvent, applyEvent]
                  have Hsa := seq_assoc ev.to_Event g.to_Event h.to_Event
                  simp [Seq.seq, Functor.map] at Hsa
                  simp [Hsa]

def bindEvent [Machine CTX M] (ev : OrdinaryEvent M γ α) (f : α → OrdinaryEvent M γ β) : OrdinaryEvent M γ β :=
  let event := ev.to_Event >>= (fun x => (f x).to_Event)
  {
    guard := event.guard
    action := event.action
    po := {
      safety := fun m x => by intros Hinv Hgrd
                              simp [bind, bind_Event, event] at *
                              have Hsafe₁ := ev.po.safety m x Hinv
                              simp [Hgrd] at Hsafe₁
                              have Hsafe₂ := (f (ev.to_Event.2 m x).fst).po.safety (ev.to_Event.2 m x).snd x Hsafe₁
                              simp [Hgrd] at Hsafe₂
                              assumption
    }
  }

instance [Machine CTX M]: Monad (OrdinaryEvent M γ) where
  bind := bindEvent

instance [Machine CTX M]: LawfulMonad (OrdinaryEvent M γ) where
  bind_pure_comp := by intros α β f ev
                       simp [pure, Functor.map, pureEvent, mapEvent, bind, bindEvent]
                       have H := bind_pure_comp  f ev.to_Event
                       simp [bind, pure, Functor.map] at H
                       simp [H]

  bind_map := by simp [bind] ; intros ; rfl
  pure_bind := by intros α β x f
                  simp only [pure]
                  simp [bind, bindEvent]
                  simp only [pure]
                  have H := pure_bind x (fun x => (f x).to_Event)
                  simp only [pure, bind] at H
                  revert H
                  cases (f x)
                  case mk ev po =>
                    simp

  bind_assoc := by intros α β γ' ev f g
                   simp [bind, bindEvent]
                   have H := bind_assoc ev.to_Event (fun x => (f x).to_Event) (fun x => (g x).to_Event)
                   simp [bind] at H
                   simp [H]

/- Category and Arrow -/

instance [Machine CTX M]: Category (OrdinaryEvent M) where
  id := funEvent M id

  comp {α β γ} (ev₂ : OrdinaryEvent M β γ) (ev₁ : OrdinaryEvent M α β) : OrdinaryEvent M α γ :=
    let event := ev₁.to_Event (>>>) ev₂.to_Event
    {
      guard := event.guard
      action := event.action
      po := {
        safety := fun m x => by simp [event]
                                intros Hinv Hgrd₁ Hgrd₂
                                have Hsafe₁ := ev₁.po.safety m x Hinv Hgrd₁
                                let ev₁' := ev₁.to_Event.action m x
                                have Hsafe₂ := ev₂.po.safety ev₁'.2 ev₁'.1
                                exact Hsafe₂ Hsafe₁ Hgrd₂
      }
    }

instance [Machine CTX M]: LawfulCategory (OrdinaryEvent M) where
  id_right {α β} (ev : OrdinaryEvent M α β) := by cases ev
                                                  simp [Category.rcomp]

  id_left {α β} (ev : OrdinaryEvent M α β) := by cases ev
                                                 simp [Category.rcomp]

  id_assoc {α β γ δ} (ev₃ : OrdinaryEvent M γ δ) (ev₂ : OrdinaryEvent M β γ) (ev₁ : OrdinaryEvent M α β) := by
      cases ev₁
      cases ev₂
      cases ev₃
      simp [Category.rcomp]
      funext m x
      simp [And_eq_assoc]

@[simp]
def OrdinaryEvent_Arrow_first [Machine CTX M] (ev : OrdinaryEvent M α β) : OrdinaryEvent M (α × γ) (β × γ) :=
  let event := Arrow.first ev.to_Event
  {
    guard := event.guard
    action := event.action
    po := {
      safety := fun m (x,_) => by simp [Arrow.first, event]
                                  intros Hinv Hgrd
                                  apply ev.po.safety m x Hinv Hgrd
    }
  }

instance [Machine CTX M]: Arrow (OrdinaryEvent M) where
  arrow {α β} (f : α → β) := funEvent M f

  split {α α' β β'} (ev₁ : OrdinaryEvent M α β)  (ev₂ : OrdinaryEvent M α' β') : OrdinaryEvent M (α × α') (β × β') :=
    Arrow.split_from_first (funEvent M (fun (x, y) => (y, x)))
                           OrdinaryEvent_Arrow_first
                           ev₁ ev₂

instance [Machine CTX M]: LawfulArrow (OrdinaryEvent M) where
  arrow_id := by simp [Arrow.arrow]
  arrow_ext _ := by simp [Arrow.arrow, Arrow.first]
  arrow_fun _ _ := by simp [Arrow.arrow, Arrow.first]
  arrow_xcg _ _ := by simp [Arrow.arrow, Arrow.first]
  arrow_unit _ := by simp [Arrow.arrow, Arrow.first]
  arrow_assoc {α β γ δ} (f : OrdinaryEvent M α β) :=
    by simp [Arrow.arrow, Arrow.first]

/- Contravariant functor -/

abbrev CoEvent (M) [Machine CTX M] (α) (β) :=
   OrdinaryEvent M β α

@[simp]
def OrdinaryEvent_from_CoEvent [Machine CTX M] (ev : CoEvent M α β) : OrdinaryEvent M β α := ev

@[simp]
def CoEvent_from_OrdinaryEvent [Machine CTX M] (ev : OrdinaryEvent M α β) : CoEvent M β α := ev


instance [Machine CTX M]: ContravariantFunctor (CoEvent M γ) where
  contramap {α β} (f : β → α) (ev : CoEvent M γ α) :=
  let event := let ev' := coEvent_from_Event ev.to_Event
             let ev'' := ContravariantFunctor.contramap f ev'
             Event_from_CoEvent ev''
  {
    guard := event.guard
    action := event.action
    po := {
      safety := fun m x => by simp [ContravariantFunctor.contramap]
                              intros Hinv Hgrd
                              exact ev.po.safety m (f x) Hinv Hgrd
    }
  }

instance [Machine CTX M] : LawfullContravariantFunctor (CoEvent M α) where
  cmap_id _ := by rfl
  cmap_comp _ _ := by rfl

/- Profunctor -/

instance [Machine CTX M] : Profunctor (OrdinaryEvent M) where
  dimap {α β} {γ δ} (f : β → α) (g : γ → δ) (ev : OrdinaryEvent M α γ) : OrdinaryEvent M β δ :=
    let event := Profunctor.dimap f g ev.to_Event
    {
      guard := event.guard
      action := event.action
      po := {
        safety := fun m x => by simp [Profunctor.dimap]
                                intros Hinv Hgrd
                                let ev' := OrdinaryEvent_from_CoEvent (ContravariantFunctor.contramap f (CoEvent_from_OrdinaryEvent ev))
                                let ev'' := g <$> ev'
                                have Hsafe := ev''.po.safety m x Hinv
                                revert Hsafe ev' ev'' ; simp
                                intro Hsafe
                                exact Hsafe Hgrd
      }
    }

instance [Machine CTX M] : LawfulProfunctor (OrdinaryEvent M) where
  dimap_id := rfl
  dimap_comp _ _ _ _ := rfl

instance [Machine CTX M] : StrongProfunctor (OrdinaryEvent M) where
  first' {α β γ} (ev : OrdinaryEvent M α β): OrdinaryEvent M (α × γ) (β × γ) :=
    let event := StrongProfunctor.first' ev.to_Event
    {
      guard := event.guard
      action := event.action
      po := {
        safety := fun m x => by simp
                                intros Hinv Hgrd
                                apply ev.po.safety <;> assumption
      }
    }

instance [Machine CTX M] : LawfulStrongProfunctor (OrdinaryEvent M) where
