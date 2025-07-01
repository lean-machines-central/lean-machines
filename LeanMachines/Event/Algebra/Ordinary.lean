import LeanMachines.Event.Prelude
import LeanMachines.Event.Basic
import LeanMachines.Event.Algebra.Basic
import LeanMachines.Algebra.Contravariant
import LeanMachines.Algebra.Profunctor
import LeanMachines.Algebra.Arrow
import LeanMachines.Event.Ordinary



/-!
## Algebraic properties of events

The following instantiate various algebraic structures, complementing
the structural properties of the representation types (`_Event`) with
more "lawful" properties for the main event type (`OrdinaryEvent`).

This part is rather experimental and is thus not fully documented yet.

-/

/- Functor -/
section Ordinary
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

instance fo [Machine CTX M] : Functor (OrdinaryEvent M γ) where
  map := mapEvent

instance [Machine CTX M] : LawfulFunctor (OrdinaryEvent M γ) where
  map_const := rfl
  id_map := by intros ; rfl
  comp_map := by intros ; rfl

end Ordinary

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
      safety := fun m x => by
        simp [event, Seq.seq, apply_Event]
        intro Hinv ⟨Hgrd₁, _⟩
        have Hsafe₁ := ef.po.safety m x Hinv Hgrd₁
        apply ev.po.safety ; assumption
    }
  }

instance [Machine CTX M]: Applicative (OrdinaryEvent M γ) where
  seq ef ev := applyEvent ef (ev ())

instance [Machine CTX M]: LawfulApplicative (OrdinaryEvent M γ) where
  map_const := by intros ; rfl
  id_map := by intros ; rfl
  seqLeft_eq := by intros ; rfl
  seqRight_eq := by intros ; rfl
  pure_seq := by
    intros
    apply OrdinaryEvent.ext
    apply pure_seq

  map_pure := by intros α β g x ; rfl

  seq_pure := by
    intros
    apply OrdinaryEvent.ext
    apply seq_pure

  seq_assoc := by
    intros
    apply OrdinaryEvent.ext
    apply seq_assoc

def bindEvent [Machine CTX M] (ev : OrdinaryEvent M γ α) (f : α → OrdinaryEvent M γ β) : OrdinaryEvent M γ β :=
  let event := ev.to_Event >>= (fun x => (f x).to_Event)
  {
    guard := event.guard
    action := event.action
    po := {
      safety := fun m x => by
        simp [event, bind]
        intros Hinv Hgrd
        simp [bind_Event] at *
        obtain ⟨Hgrd₁, Hgrd₂'⟩ := Hgrd
        have Hgrd₂ := Hgrd₂' Hgrd₁
        simp at Hgrd₂
        have Hsafe₁ := ev.po.safety m x Hinv Hgrd₁
        apply (f (ev.action m x Hgrd₁).fst).po.safety ; assumption
    }
  }

instance [Machine CTX M]: Monad (OrdinaryEvent M γ) where
  bind := bindEvent

theorem OrdinaryEvent_liftBind [Machine CTX M] (ev : OrdinaryEvent M γ α) (f : α → OrdinaryEvent M γ β):
  (ev >>= f).to_Event = (ev.to_Event >>= fun x => (f x).to_Event) :=
by
  simp [bind, bindEvent]

instance [Machine CTX M]: LawfulMonad (OrdinaryEvent M γ) where
  bind_pure_comp := by
    intros
    apply OrdinaryEvent.ext
    apply bind_pure_comp

  bind_map := by simp [bind] ; intros ; rfl

  pure_bind := by
    intros
    apply OrdinaryEvent.ext
    simp [OrdinaryEvent_liftBind]
    apply pure_bind

  bind_assoc := by
    intros
    apply OrdinaryEvent.ext
    simp [OrdinaryEvent_liftBind]

/- Category and Arrow -/

instance [Machine CTX M]: Category (OrdinaryEvent M) where
  id := funEvent M id

  comp {α β γ} (ev₂ : OrdinaryEvent M β γ) (ev₁ : OrdinaryEvent M α β) : OrdinaryEvent M α γ :=
    let event := ev₁.to_Event (>>>) ev₂.to_Event
    {
      guard := event.guard
      action := event.action
      po := {
        safety := fun m x => by
          simp [event]
          intro Hinv ⟨Hgrd₁, Hgrd₂'⟩
          have Hsafe₁ := ev₁.po.safety m x Hinv Hgrd₁
          apply ev₂.po.safety ; assumption
      }
    }

instance [Machine CTX M]: LawfulCategory (OrdinaryEvent M) where
  id_right _ := by
    apply OrdinaryEvent.ext
    apply LawfulCategory.id_right

  id_left _ := by
    apply OrdinaryEvent.ext
    apply LawfulCategory.id_left

  id_assoc _ _ _ := by
    apply OrdinaryEvent.ext
    apply LawfulCategory.id_assoc

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
  arrow {α β} (f : α → β) := {
    to_Event := Arrow.arrow f
    po := {
      safety := fun m x => by simp [Arrow.arrow]
    }
  }

  split {α α' β β'} (ev₁ : OrdinaryEvent M α β)  (ev₂ : OrdinaryEvent M α' β') : OrdinaryEvent M (α × α') (β × β') :=
  {
    to_Event := Arrow.split ev₁.to_Event ev₂.to_Event
    po := {
      safety := fun m (x, x') => by
        simp [Arrow.split]
        intro Hinv ⟨Hgrd₁, Hgrd₂⟩
        let m'₁ := (ev₁.action m x Hgrd₁).snd
        let m'₂ := (ev₂.action m'₁ x' (Hgrd₂ Hgrd₁)).snd
        exact ev₂.po.safety m'₁ x' (ev₁.po.safety m x Hinv Hgrd₁) (Hgrd₂ Hgrd₁)
    }
  }

def OrdinaryEvent.arrM [Machine CTX M] (f : M → α → β ) : OrdinaryEvent M α β :=
  {
    to_Event := _Event.arrM f
    po := {
      safety := fun m x =>
      by
        simp[_Event.arrM]
    }
  }


theorem OrdinaryEvent_lift_arrow [Machine CTX M] (f : α → β):
  (instArrowOrdinaryEvent.arrow f).to_Event (M := M) = Arrow.arrow f :=
by
  simp [Arrow.arrow]

theorem OrdinaryEvent_lift_split [Machine CTX M] {α α' β β'} (ev₁ : OrdinaryEvent M α β) (ev₂ : OrdinaryEvent M α' β'):
  (instArrowOrdinaryEvent.split ev₁ ev₂).to_Event
  = Arrow.split ev₁.to_Event ev₂.to_Event :=
by
  simp [Arrow.split, Arrow.first]

theorem OrdinaryEvent_lift_first [Machine CTX M] {α β} (ev : OrdinaryEvent M α β):
  (instArrowOrdinaryEvent.first ev (γ:=γ)).to_Event
  = Arrow.first (ev.to_Event) :=
by
  exact rfl

instance [Machine CTX M]: LawfulArrow (OrdinaryEvent M) where
  arrow_id := by simp [Arrow.arrow]
  arrow_ext {α β γ} f := by
    apply OrdinaryEvent.ext
    apply LawfulArrow.arrow_ext

  arrow_fun _ _ := by
    apply OrdinaryEvent.ext
    apply LawfulArrow.arrow_fun

  arrow_xcg _ _ := by
    apply OrdinaryEvent.ext
    apply LawfulArrow.arrow_xcg

  arrow_unit _ := by
    apply OrdinaryEvent.ext
    apply LawfulArrow.arrow_unit

  arrow_assoc {α β γ δ} (f : OrdinaryEvent M α β) := by
    apply OrdinaryEvent.ext
    apply LawfulArrow.arrow_assoc



instance [Machine CTX M] : ArrowChoice (OrdinaryEvent M) where
  splitIn ev₁ ev₂ :=
    {
      to_Event := alt_Event ev₁.to_Event ev₂.to_Event
      po := {
        safety m x hinv hgrd :=
        match x with
        | .inl a => ev₁.po.safety m a hinv hgrd
        | .inr b =>ev₂.po.safety m b hinv hgrd
      }
    }

instance [Machine CTX M]: LawfulArrowChoice (OrdinaryEvent M) where
  left_arr f :=
    by
      apply OrdinaryEvent.ext
      apply LawfulArrowChoice.left_arr
  left_f_g f g :=
    by
      apply OrdinaryEvent.ext
      apply LawfulArrowChoice.left_f_g
  arr_inl f :=
    by
      apply OrdinaryEvent.ext
      apply LawfulArrowChoice.arr_inl
  split f g :=
    by
      apply OrdinaryEvent.ext
      apply LawfulArrowChoice.split
  assoc f :=
    by
      apply OrdinaryEvent.ext
      apply LawfulArrowChoice.assoc


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
      safety := fun m x => by
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
        safety := fun m x => by
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
        safety := fun m x => by intros Hinv Hgrd
                                apply ev.po.safety <;> assumption
      }
    }

instance [Machine CTX M] : LawfulStrongProfunctor (OrdinaryEvent M) where
  dimap_pi_id a :=
  by
    simp[Profunctor.dimap,StrongProfunctor.first']
  first_first a :=
  by
    simp[Profunctor.dimap,StrongProfunctor.first',α_,α_inv]
  dinaturality a f :=
  by
    simp[Profunctor.dimap,StrongProfunctor.first']
