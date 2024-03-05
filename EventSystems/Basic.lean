import EventSystems.Prelude

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
  guard : M → α → Prop

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

def skip_Event (M) [Machine CTX M] (α) : _Event M α α :=
  { guard := fun _ _ => True
    action := fun m x => (x, m)
  }

def fun_Event  (M) [Machine CTX M] (f : α → β) : _Event M α β :=
{
  guard := fun _ _ => True
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
  comp_map := by intros α β γ g h x
                 simp [Functor.map, map_Event]

/- Applicative Functor -/

@[simp]
def pure_Event [Machine CTX M] (y : α) : _Event M γ α :=
  { guard := fun m x => True
    action := fun m x => (y, m)
  }

instance [Machine CTX M]: Pure (_Event M γ) where
  pure := pure_Event

/- XXX : this one does not respect seq_pure -/
@[simp]
def apply_Event_bad [Machine CTX M] (ef : _Event M γ (α → β)) (ev : _Event M γ α) : _Event M γ β :=
  {
    guard := fun m x => ef.guard m x ∧ ev.guard m x
    action := fun m x => let (f, m') := ef.action m x
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
  pure_bind := by intros α β x f
                  simp [pure, bind, bind_Event]
  bind_assoc := by intros β γ' x f g h
                   simp [bind, bind_Event]
                   funext
                   apply And_eq_assoc

structure _EventPO [Machine CTX M] (ev : _Event M α β) (kind : EventKind) where
  safety (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → Machine.invariant (ev.action m x).snd

structure OrdinaryEvent (M) [Machine CTX M] (α) (β) where
  event : _Event M α β
  po : _EventPO event (EventKind.TransDet Convergence.Ordinary)

structure EventSpec (M) [Machine CTX M] (α) (β) where
  guard (m : M) (x : α) : Prop
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
  { event := _Event_from_EventSpec ev
    po := { safety := fun m x => by simp
                                    intros Hinv Hgrd
                                    apply ev.safety <;> assumption
    }
  }

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

def funEventSpec [Machine CTX M] (f : α → β) : EventSpec M α β :=
{
  guard := fun _ _ => True
  action := fun m x => (f x, m)
  safety := fun m x => by simp
}

def funEvent (M) [Machine CTX M] (f : α → β) : OrdinaryEvent M α β :=
  newEvent (EventSpec_from_Event (fun_Event M f)
                                 (fun m x Hinv _ => by simp [fun_Event] ; assumption))

def mapEvent [Machine CTX M] (f : α → β) (ev : OrdinaryEvent M γ α) : OrdinaryEvent M γ β :=
{
  event := Functor.map f ev.event
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
  { event := pure y
    po := {
      safety := fun m _ => by simp [pure]
    }
  }

instance [Machine CTX M]: Pure (OrdinaryEvent M γ) where
  pure := pureEvent

def applyEvent [Machine CTX M] ( ef : OrdinaryEvent M γ (α → β)) (ev : OrdinaryEvent M γ α) : OrdinaryEvent M γ β :=
  { event := ef.event <*> ev.event
    po := {
      safety := fun m x => by simp [Seq.seq, apply_Event]
                              intros Hinv Hgrd₁ Hgrd₂
                              have Hsafe₁ := ef.po.safety m x Hinv Hgrd₁
                              apply ev.po.safety (ef.event.action m x).snd
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
                   simp [Seq.seq, pure, Functor.map]
                   simp [applyEvent, mapEvent]
                   constructor
                   · apply pure_seq
                   · apply heq_of_eqRec_eq
                     · simp
                     · simp [Seq.seq, apply_Event]
                       cases ev
                       case mk evr act =>
                         simp [Functor.map, map_Event]

  map_pure := by intros α β g x ; rfl
  seq_pure := by intros α β ev x
                 simp [Seq.seq, pure, Functor.map]
                 simp [applyEvent, mapEvent]
                 constructor
                 · apply seq_pure
                 · apply cast_heq
                 · apply heq_of_eqRec_eq
                   · simp
                   · simp [Seq.seq, apply_Event]
                     cases ev
                     case mk evr act =>
                       simp [Functor.map, map_Event]

  seq_assoc := by intros α β γ' ev g h
                  simp [Seq.seq, Functor.map, mapEvent, applyEvent]
                  constructor
                  · apply seq_assoc
                  · apply cast_heq
                    have Hsa := seq_assoc ev.event g.event h.event
                    simp [Seq.seq, Functor.map] at Hsa
                    rw [Hsa]
