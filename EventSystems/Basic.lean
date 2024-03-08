import EventSystems.Prelude
import EventSystems.Classes

def hello := "world"

class Machine (CTX : outParam (Type u)) (M) where
  context : CTX
  invariant : M → Prop

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

structure _EventRoot (M) [Machine CTX M] (α : Type 0) where
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

  action: M → α → (β × M)

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

/- Functor -/

def map_Event [Machine CTX M] (f : α → β) (ev : _Event M γ α)  : _Event M γ β :=
  { guard := ev.guard
    action := fun m x => let (y, m') := ev.action m x
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

instance [Machine CTX M]: Arrow (_Event M) where
  arrow {α β} (f : α → β) := fun_Event M f

  split {α α' β β'} (ev₁ : _Event M α β)  (ev₂ : _Event M α' β') : _Event M (α × α') (β × β') :=
    Arrow.split_from_first (fun_Event M (fun (x, y) => (y, x)))
                           _Event_Arrow_first
                           ev₁ ev₂

instance [Machine CTX M]: LawfulArrow (_Event M) where
  arrow_id := by simp [Arrow.arrow]
  arrow_ext _ := by simp [Arrow.arrow, Arrow.first]
  arrow_fun _ _ := by simp [Arrow.arrow, Arrow.first]
  arrow_xcg _ _ := by simp [Arrow.arrow, Arrow.first]
  arrow_unit _ := by simp [Arrow.arrow, Arrow.first]
  arrow_assoc {α β γ δ} (f : _Event M α β) :=
    by simp [Arrow.arrow, Arrow.first]

/- Contravariant functor -/

abbrev _CoEvent (M) [Machine CTX M] (α) (β) :=
  _Event M β α

@[simp]
def coEvent_from_Event [Machine CTX M] (ev : _Event M α β) : _CoEvent M β α :=
 ev

@[simp]
def Event_from_CoEvent [Machine CTX M] (ev : _CoEvent M β α) : _Event M α β :=
 ev

instance [Machine CTX M] : Contravariant (_CoEvent M β) where
  contramap f ev := { guard := fun m x => ev.guard m (f x)
                      action := fun m x => ev.action m (f x)
                    }

instance [Machine CTX M] : LawfullContravariant (_CoEvent M β) where
  cmap_id _ := rfl
  cmap_comp _ _ := rfl

/- Profunctor -/

instance [Machine CTX M] : Profunctor (_Event M) where
  dimap {α β} {γ δ} (f : β → α) (g : γ → δ) (ev : _Event M α γ) : _Event M β δ :=
    let ev' := Event_from_CoEvent (Contravariant.contramap f (coEvent_from_Event ev))
    Functor.map g ev'

instance [Machine CTX M] : LawfulProfunctor (_Event M) where
  dimap_id _ := rfl
  dimap_comp _ _ _ _ _ := rfl

/- Ordinary events -/

structure _EventPO [Machine CTX M] (ev : _Event M α β) (kind : EventKind) where
  safety (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → Machine.invariant (ev.action m x).snd

structure OrdinaryEvent (M) [Machine CTX M] (α) (β) extends _Event M α β where
  --event : _Event M α β
  po : _EventPO to_Event  (EventKind.TransDet Convergence.Ordinary)

structure EventSpec (M) [Machine CTX M] (α) (β) where
  guard (m : M) (x : α) : Prop := True
  action (m : M) (x : α) : β × M
  safety (m : M) (x : α) :
    Machine.invariant m
    → guard m x
    → Machine.invariant (action m x).snd

@[simp]
def _Event_from_EventSpec [Machine CTX M] (ev : EventSpec M α β) : _Event M α β :=
  { guard := ev.guard
    action := ev.action
  }

@[simp]
def newEvent {M} [Machine CTX M] (ev : EventSpec M α β) : OrdinaryEvent M α β :=
  let event := _Event_from_EventSpec ev
  { guard := event.guard
    action := event.action
    po := { safety := fun m x => by simp
                                    intros Hinv Hgrd
                                    apply ev.safety <;> assumption
    }
  }

@[simp]
def EventSpec_from_Event [Machine CTX M]
  (ev : _Event M α β)
  (Hsafe : (m : M) → (x : α) →  Machine.invariant m
                           → ev.guard m x
                           → Machine.invariant (ev.action m x).snd) : EventSpec M α β :=
  { guard := ev.guard
    action := ev.action
    safety := Hsafe
  }

def skipEvent (M) [Machine CTX M] (α) : OrdinaryEvent M α α :=
  newEvent (EventSpec_from_Event (skip_Event M α)
                                 (by intros ; simp [skip_Event] ; assumption))

@[simp]
def funEvent (M) [Machine CTX M] (f : α → β) : OrdinaryEvent M α β :=
  newEvent (EventSpec_from_Event (fun_Event M f)
                                 (fun m x Hinv _ => by simp [fun_Event] ; assumption))

def mapEvent [Machine CTX M] (f : α → β) (ev : OrdinaryEvent M γ α) : OrdinaryEvent M γ β :=
  let event := Functor.map f ev.to_Event
  {
    guard := event.guard
    action := event.action
    po := { safety := fun m x => by intros Hinv Hgrd
                                    simp [Functor.map, map_Event] at *
                                    apply ev.po.safety m x Hinv Hgrd
  }
}

instance [Machine CTX M] : Functor (OrdinaryEvent M γ) where
  map := mapEvent

instance [Machine CTX M] : LawfulFunctor (OrdinaryEvent M γ) where
  map_const := by intros ; rfl
  id_map := by intros ; rfl
  comp_map := by intros ; rfl

/- Applicative Functor -/

@[simp]
def pureEvent [Machine CTX M] (y : α) : OrdinaryEvent M γ α :=
  let event : _Event M γ α := pure y
  {
    guard := event.guard
    action := event.action
    po := {
      safety := fun m _ => by simp [event, pure]
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
                   simp only [Seq.seq, applyEvent, pure, pureEvent, Functor.map, mapEvent]
                   simp
                   constructor
                   · have Hps := pure_seq g ev
                     simp [Seq.seq, pure, Functor.map] at Hps
                     simp [Hps]
                   apply cast_heq
                   simp [map_Event, apply_Event]

  map_pure := by intros α β g x ; rfl
  seq_pure := by intros α β ev x
                 simp [Seq.seq, pure, Functor.map]
                 simp [applyEvent, mapEvent]
                 constructor
                 · have Hsp := seq_pure ev.to_Event x
                   simp [Functor.map, Seq.seq, pure] at *
                   simp [Hsp]
                 apply cast_heq
                 simp [Seq.seq, Functor.map, map_Event, apply_Event]

  seq_assoc := by intros α β γ' ev g h
                  simp [Seq.seq, Functor.map, mapEvent, applyEvent]
                  have Hsa := seq_assoc ev.to_Event g.to_Event h.to_Event
                  simp [Seq.seq, Functor.map] at Hsa
                  constructor
                  · simp [Hsa]
                  apply cast_heq
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
                       constructor
                       · simp [H]
                       · apply cast_heq
                         rw [H]

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
                    intro H
                    constructor
                    · assumption
                    · apply cast_heq
                      rw [←H]

  bind_assoc := by intros α β γ' ev f g
                   simp [bind, bindEvent]
                   have H := bind_assoc ev.to_Event (fun x => (f x).to_Event) (fun x => (g x).to_Event)
                   simp [bind] at H
                   constructor
                   · simp [H]
                   apply cast_heq
                   rw [H]

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
                                                  apply cast_heq ; simp

  id_left {α β} (ev : OrdinaryEvent M α β) := by cases ev
                                                 simp [Category.rcomp]
                                                 apply cast_heq ; simp

  id_assoc {α β γ δ} (ev₃ : OrdinaryEvent M γ δ) (ev₂ : OrdinaryEvent M β γ) (ev₁ : OrdinaryEvent M α β) := by
      cases ev₁
      cases ev₂
      cases ev₃
      simp [Category.rcomp]
      constructor
      · funext m x
        simp [And_eq_assoc]
      · apply cast_heq
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
                    apply cast_heq ; simp
  arrow_fun _ _ := by simp [Arrow.arrow, Arrow.first]
                      apply cast_heq ; simp
  arrow_xcg _ _ := by simp [Arrow.arrow, Arrow.first]
                      apply cast_heq ; simp
  arrow_unit _ := by simp [Arrow.arrow, Arrow.first]
                     apply cast_heq ; simp
  arrow_assoc {α β γ δ} (f : OrdinaryEvent M α β) :=
    by simp [Arrow.arrow, Arrow.first]
       apply cast_heq ; simp

/- Contravariant functor -/

abbrev CoEvent (M) [Machine CTX M] (α) (β) :=
   OrdinaryEvent M β α

@[simp]
def OrdinaryEvent_from_CoEvent [Machine CTX M] (ev : CoEvent M α β) : OrdinaryEvent M β α := ev

@[simp]
def CoEvent_from_OrdinaryEvent [Machine CTX M] (ev : OrdinaryEvent M α β) : CoEvent M β α := ev


instance [Machine CTX M]: Contravariant (CoEvent M γ) where
  contramap {α β} (f : β → α) (ev : CoEvent M γ α) :=
  let event := let ev' := coEvent_from_Event ev.to_Event
             let ev'' := Contravariant.contramap f ev'
             Event_from_CoEvent ev''
  {
    guard := event.guard
    action := event.action
    po := {
      safety := fun m x => by simp [Contravariant.contramap]
                              intros Hinv Hgrd
                              exact ev.po.safety m (f x) Hinv Hgrd
    }
  }

instance [Machine CTX M] : LawfullContravariant (CoEvent M α) where
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
                                let ev' := OrdinaryEvent_from_CoEvent (Contravariant.contramap f (CoEvent_from_OrdinaryEvent ev))
                                let ev'' := g <$> ev'
                                have Hsafe := ev''.po.safety m x Hinv
                                revert Hsafe ev' ev'' ; simp
                                intro Hsafe
                                exact Hsafe Hgrd
      }
    }

instance [Machine CTX M] : LawfulProfunctor (OrdinaryEvent M) where
  dimap_id _ := rfl
  dimap_comp _ _ _ _ _ := rfl
