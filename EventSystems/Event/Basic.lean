import EventSystems.Event.Prelude
import EventSystems.Algebra.Contravariant
import EventSystems.Algebra.Profunctor
import EventSystems.Algebra.Arrow

def hello := "world"

class Machine (CTX : outParam (Type u)) (M) where
  context : CTX
  invariant : M → Prop
  reset : M

inductive Convergence where
  | Ordinary
  | Convergent
  | Anticipated
  deriving Repr, BEq, DecidableEq

inductive EventKind where
  | InitDet
  | InitNonDet
  | TransDet (status : Convergence)
  | TransNonDet (status : Convergence)
  deriving Repr, BEq, DecidableEq

open EventKind

structure _EventRoot (M) [Machine CTX M] (α : Type) where
  guard : M → α → Prop := fun _ _ => True

theorem ext_EventRoot [Machine CTX M] (ev1 ev2 : _EventRoot M α):
  ev1.guard = ev2.guard
  → ev1 = ev2 :=
by
  intro H
  cases ev1
  cases ev2
  simp [*] at *
  simp [*]

structure _Event (M) [Machine CTX M] (α) (β : Type)
  extends _EventRoot M α where

  -- TODO : ensure in action that the guard is true ?
  -- action (m : M) (x : α) {grd: guard m x}: (β × M)
  action (m : M) (x : α): (β × M)

structure _InitEvent (M) [Machine CTX M] (α) (β : Type) where
  guard : α → Prop
  init: α → (β × M)

@[simp]
def _InitEvent.to_Event [Machine CTX M] (ev : _InitEvent M α β) : _Event M α β :=
  {
    guard := fun m x => m = Machine.reset ∧ ev.guard x
    action := fun _ x => ev.init x
  }

theorem ext_Event [Machine CTX M] (ev1 ev2 : _Event M α β):
  ev1.guard = ev2.guard → ev1.action = ev2.action
  → ev1 = ev2 :=
by
  intro H₁ H₂
  have Hr := ext_EventRoot ev1.to_EventRoot ev2.to_EventRoot H₁
  cases ev1
  cases ev2
  simp [*] at *
  simp [*]

@[simp]
def skip_Event (M) [Machine CTX M] (α) : _Event M α α :=
{
  action := fun m x => (x, m)
}

@[simp]
def fun_Event  (M) [Machine CTX M] (f : α → β) : _Event M α β :=
{
  action := fun m x => (f x, m)
}

@[simp]
def funskip_Event (M) [Machine CTX M] (xf : M → α → β) : _Event M α β :=
{
  action := fun m x => (xf m x, m)
}

/- Functor -/

def map_Event [Machine CTX M] (f : α → β) (ev : _Event M γ α)  : _Event M γ β :=
  { guard := ev.guard
    action := fun m x => let (y, m') := (ev.action m x)
                         (f y, m')
   }

instance [Machine CTX M]: Functor (_Event M γ) where
  map := map_Event

instance [Machine CTX M]: LawfulFunctor (_Event M γ) where
  map_const := by intros α β
                  simp [Functor.mapConst, Functor.map]
  id_map := by intros α ev
               simp [Functor.map, map_Event]
  comp_map := by intros α _ γ g h x
                 simp [Functor.map, map_Event]

/- Applicative Functor -/

@[simp]
def pure_Event [Machine CTX M] (y : α) : _Event M γ α :=
  {
    action := fun m _ => (y, m)
  }

instance [Machine CTX M]: Pure (_Event M γ) where
  pure := pure_Event

/- XXX : this one does not respect seq_pure -/
def apply_Event_bad [Machine CTX M] (ef : _Event M γ (α → β)) (ev : _Event M γ α) : _Event M γ β :=
  {
    guard := fun m x => ef.guard m x ∧ ev.guard m x
    action := fun m x => let (f, _) := ef.action m x
                         let (y, m'') := ev.action m x
                         (f y, m'')
  }

def apply_Event [Machine CTX M] ( ef : _Event M γ (α → β)) (ev : _Event M γ α) : _Event M γ β :=
  {
    guard := fun m x => ef.guard m x ∧ ev.guard (ef.action m x).snd x
    action := fun m x => let (f, m') := ef.action m x
                         let (y, m'') := ev.action m' x
                         (f y, m'')
  }

instance [Machine CTX M]: Applicative (_Event M γ) where
  seq ef ev := apply_Event ef (ev ())

instance [Machine CTX M]: LawfulApplicative (_Event M γ) where
  map_const := by intros ; rfl
  id_map := by intros ; rfl
  seqLeft_eq := by intros ; rfl
  seqRight_eq := by intros ; rfl
  pure_seq := by intros α β g x
                 simp [Seq.seq, Functor.map, map_Event, pure, pure_Event, apply_Event]
  map_pure := by intros α β g x ; rfl
  seq_pure := by intros α β ev x
                 simp [Seq.seq, pure, Functor.map, map_Event, apply_Event]
  seq_assoc := by intros α β γ' ev g h
                  simp [Seq.seq, Functor.map, map_Event, apply_Event]
                  funext m y
                  rw [And_eq_assoc]

/- Monad -/

def bind_Event [Machine CTX M] (ev : _Event M γ α) (f : α → _Event M γ β) : _Event M γ β :=
  {
    guard := fun m x => ev.guard m x ∧ let (y, m') := ev.action m x
                                       let ev' := f y
                                       ev'.guard m' x
    action := fun m x => let (y, m') := ev.action m x
                         let ev' := f y
                         ev'.action m' x
  }


instance [Machine CTX M]: Monad (_Event M γ) where
  bind := bind_Event

instance [Machine CTX M]: LawfulMonad (_Event M γ) where
  bind_pure_comp := by intros α β f ev
                       simp [pure, Functor.map, pure_Event, map_Event, bind, bind_Event]
  bind_map := by simp [bind] ; intros ; rfl
  pure_bind := by intros _ β x f
                  simp [pure, bind, bind_Event]
  bind_assoc := by intros β γ' x f g h
                   simp [bind, bind_Event]
                   funext
                   apply And_eq_assoc

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

-- Arrows are less poweful (but more general) than Monads
-- but Events are monads in their output type
-- and both monads and arrows do not apply on input types

instance [Machine CTX M]: Category (_Event M) where
  id := fun_Event M id

  comp {α β γ} (ev₂ : _Event M β γ) (ev₁ : _Event M α β) : _Event M α γ :=
    { guard := fun m x => ev₁.guard m x ∧ let (y, m') := ev₁.action m x
                                          ev₂.guard m' y
      action := fun m x => let (y, m') := ev₁.action m x
                           ev₂.action m' y
    }

instance [Machine CTX M]: LawfulCategory (_Event M) where
  id_right _ := by simp
  id_left _ := by simp
  id_assoc _ _ _ := by simp ; funext m x ; apply And_eq_assoc

@[simp]
def _Event_Arrow_first [Machine CTX M] (ev : _Event M α β) : _Event M (α × γ) (β × γ) :=
  { guard := fun m (x, _) => ev.guard m x
    action := fun m (x, y) => let (x', m') := ev.action m x
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
    action := fun m x => (f x, m)
  }

  split {α α' β β'} (ev₁ : _Event M α β)  (ev₂ : _Event M α' β') : _Event M (α × α') (β × β') := {
    guard := fun m (x, y) => ev₁.guard m x ∧ ev₂.guard m y
    action := fun m (x, y) => let (x',m') := ev₁.action m x
                              let (y', _) := ev₂.action m y
                              -- note : we forget the second state change
                              ((x', y'), m')
  }



instance [Machine CTX M]: LawfulArrow (_Event M) where
  arrow_id := by simp [Arrow.arrow]
  arrow_ext _ := by simp [Arrow.arrow, Arrow.first]
  arrow_fun _ _ := by simp [Arrow.arrow, Arrow.first]
  arrow_xcg _ _ := by simp [Arrow.arrow, Arrow.first]
  arrow_unit _ := by simp [Arrow.arrow, Arrow.first]
  arrow_assoc {α β γ δ} (f : _Event M α β) :=
    by simp [Arrow.arrow, Arrow.first]

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
  dimap_id := rfl
  dimap_comp _ _ _ _ := rfl

instance [Machine CTX M] : StrongProfunctor (_Event M) where
  first' {α β γ} (ev : _Event M α β): _Event M (α × γ) (β × γ) :=
    {
      guard := fun m (x, _) => ev.guard m x
      action := fun m (x, y) => let (x', m') := ev.action m x
                                ((x', y), m')
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
                        | left l => let (y, m') := evl.action m l
                                    (left y, m')
                        | right r => let (y, m') := evr.action m r
                                    (right y, m')
  }
