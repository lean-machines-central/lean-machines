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

structure _InitEvent (M) [Machine CTX M] (α) where
  kind : EventKind
  guard : α → Prop

structure InitEvent (M) [Machine CTX M] (α)
  extends _InitEvent M α where

  init: α → M

  safety (x : α):
    guard x
    → Machine.invariant (init x)

structure InitEventSpec (M) [Machine CTX M] (α) where
  guard (x : α) : Prop
  init (x : α) : M
  safety (x : α) :
    guard x
    → Machine.invariant (init x)

@[simp]
def newInitEvent [Machine CTX M] (ev : InitEventSpec M α) : InitEvent M α :=
  { kind := EventKind.InitDet
    guard := ev.guard
    init := ev.init
    safety := ev.safety
    }

structure InitEventSpec' (M) [Machine CTX M] where
  init : M
  safety:
    Machine.invariant init

@[simp]
def newInitEvent' [Machine CTX M] (ev : InitEventSpec' M) : InitEvent M Unit :=
  { kind := EventKind.InitDet
    guard := fun _ => True
    init := fun _ => ev.init
    safety := fun _ => fun _ => ev.safety
    }

structure _Event (M) [Machine CTX M] (α : Type 0) where
  kind : EventKind
  guard : M → α → Prop

structure Event (M) [Machine CTX M] (α) (β)
  extends _Event M α where

  action: M → α → (β × M)

  safety (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → Machine.invariant (action m x).snd

@[simp]
def Event.convergent? [Machine CTX M] (ev : _Event M α)  :=
  match ev.kind with
  | EventKind.TransDet Convergence.Convergent => true
  | EventKind.TransNonDet Convergence.Convergent => true
  | _ => false

@[simp]
def Event.deterministic? [Machine CTX M] (ev : _Event M α)  :=
  match ev.kind with
  | EventKind.TransDet _ => true
  | _ => false

structure OrdinaryEvent (M) [Machine CTX M] (α) (β)
  extends Event M α β where

  kind_prop : kind = EventKind.TransDet Convergence.Ordinary

structure EventSpec (M) [Machine CTX M] (α) (β) where
  guard (m : M) (x : α) : Prop
  action (m : M) (x : α) : β × M
  safety (m : M) (x : α) :
    Machine.invariant m
    → guard m x
    → Machine.invariant (action m x).snd

@[simp]
def newEvent {M} [Machine CTX M] (ev : EventSpec M α β) : OrdinaryEvent M α β :=
  { kind := EventKind.TransDet Convergence.Ordinary
    guard := ev.guard
    action := ev.action
    safety := ev.safety
    kind_prop := by simp
    }

def SkipEvent {M} [Machine CTX M] (α) : OrdinaryEvent M α α := newEvent {
  guard := fun _ _ => True
  action := fun m x => (x, m)
  safety := fun m _ => by simp
}

structure EventSpec' (M) [Machine CTX M] where
  guard (m : M) : Prop
  action (m : M) : M
  safety (m : M):
    Machine.invariant m
    → guard m
    → Machine.invariant (action m)

@[simp]
def newEvent' {M} [Machine CTX M] (ev : EventSpec' M) : OrdinaryEvent M Unit Unit :=
  { kind := EventKind.TransDet Convergence.Ordinary
    guard := fun m _ => ev.guard m
    action := fun m _ => ((), ev.action m)
    safety := fun m _ => ev.safety m
    kind_prop := by simp
    }

def SkipEvent' {M} [Machine CTX M] : OrdinaryEvent M Unit Unit := newEvent' {
  guard := fun _ => True
  action := fun m => m
  safety := fun m => by simp
}

/- Functor -/

def mapEvent [Machine CTX M] (f : α → β) (ev : Event M γ α)  : Event M γ β :=
  { kind := ev.kind
    guard := ev.guard
    action := fun m x => let (y, m') := ev.action m x
                         (f y, m')
    safety := fun m x => by simp
                            intros Hinv Hgrd
                            apply ev.safety m x Hinv Hgrd
   }

instance [Machine CTX M]: Functor (Event M γ) where
  map := mapEvent

instance [Machine CTX M]: LawfulFunctor (Event M γ) where
  map_const := by intros α β
                  simp [Functor.mapConst, Functor.map]
  id_map := by intros α ev
               simp [Functor.map, mapEvent]
  comp_map := by intros α β γ g h x
                 simp [Functor.map, mapEvent]

/- Applicative Functor -/

def pureOrdinaryEvent [Machine CTX M] (y : α) : OrdinaryEvent M γ α :=
  { kind := EventKind.TransDet Convergence.Ordinary
    guard := fun m x => True
    action := fun m x => (y, m)
    safety := fun m x => by simp
    kind_prop := by simp
  }

instance [Machine CTX M]: Pure (OrdinaryEvent M γ) where
  pure := pureOrdinaryEvent

def applyOrdinaryEvent₁ [Machine CTX M] ( ef : OrdinaryEvent M γ (α → β)) (ev : OrdinaryEvent M γ α) : OrdinaryEvent M γ β :=
  {
    kind := EventKind.TransDet Convergence.Ordinary
    guard := fun m x => ef.guard m x ∧ ev.guard m x
    action := fun m x => let (f, m') := ef.action m x
                         let (y, m'') := ev.action m x
                         (f y, m'')
    safety := fun m x => by simp
                            intros Hinv Hgrd₁ Hgrd₂
                            apply ev.safety m x Hinv Hgrd₂

    kind_prop := by simp
  }

-- instance [Machine CTX M]: Pure (OrdinaryEvent M γ) where


def applyOrdinaryEvent₂ [Machine CTX M] ( ef : OrdinaryEvent M γ (α → β)) (ev : OrdinaryEvent M γ α) : OrdinaryEvent M γ β :=
  {
    kind := EventKind.TransDet Convergence.Ordinary
    guard := fun m x => ef.guard m x ∧ ev.guard (ef.action m x).snd x
    action := fun m x => let (f, m') := ef.action m x
                         let (y, m'') := ev.action m' x
                         (f y, m'')
    safety := fun m x => by simp
                            intros Hinv Hgrd₁ Hgrd₂
                            have Hsafe₁ := ef.safety m x Hinv Hgrd₁
                            apply ev.safety <;> assumption

    kind_prop := by simp
  }

/- Monad -/

def bindOrdinaryEvent [Machine CTX M] (f : α → OrdinaryEvent M γ β) (ev : OrdinaryEvent M γ α) : OrdinaryEvent M γ β :=
  {
    kind := EventKind.TransDet Convergence.Ordinary
    guard := fun m x => ev.guard m x ∧ let (y, m') := ev.action m x
                                       let ev' := f y
                                       ev'.guard m' x
    action := fun m x => let (y, m') := ev.action m x
                         let ev' := f y
                         ev'.action m' x
    safety := fun m x => by simp
                            intros Hinv Hgrd₁ Hgrd₂
                            have Hsafe₁ := ev.safety m x Hinv Hgrd₁
                            let nxt := ev.action m x
                            apply (f nxt.1).safety nxt.2 x Hsafe₁ Hgrd₂
    kind_prop := by simp
  }
