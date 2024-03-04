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

structure _Event (M) [Machine CTX M] (α) (β)
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

def Skip_Event [Machine CTX M] (α) : _Event M α α :=
  { guard := fun _ _ => True
    action := fun m x => (x, m)
  }

def Fun_Event  [Machine CTX M] (f : α → β) : _Event M α β :=
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

theorem pure_bind_Event [Machine CTX M] (x : α) (f : α → _Event M γ β) :
  bind_Event (pure_Event x) f = f x :=
by
  simp [pure_Event, bind_Event]


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
