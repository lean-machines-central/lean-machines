import LeanMachines.Event.Prelude
import LeanMachines.Event.Basic
import LeanMachines.Algebra.Contravariant
import LeanMachines.Algebra.Profunctor
import LeanMachines.Algebra.Arrow
import LeanMachines.Event.Ordinary




/-!
## Algebraic properties of events

The following instantiate various algebraic structures, complementing
the structural properties of the representation types (`Event`) with
more "lawful" properties for the main event type (`OrdinaryEvent`).

This part is rather experimental and is thus not fully documented yet.

-/

/- Functor -/

@[simp]
def funEvent (M) [Machine CTX M] (f : α → β) : OrdinaryEvent M α β :=
  ((fun_Event M f).toOrdinaryEvent
                                 (fun m x Hinv _ => by simp [fun_Event] ; assumption))

def mapEvent [Machine CTX M] (f : α → β) (ev : OrdinaryEvent M γ α)  : OrdinaryEvent M γ β :=
  {
    guard := ev.guard
    action := fun m x grd =>
      let (r,m) := ev.action m x grd
      (f r, m)
    safety := fun m x =>
      by
        intros hinv hgrd
        simp
        have hsafe := ev.safety
        apply hsafe
        exact hinv
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
    guard := fun _ _ => True
    action := fun m x hgrd => (y,m)
    safety :=
      by
        intro m x hinv hgrd
        simp
        exact hinv
  }

instance [Machine CTX M]: Pure (OrdinaryEvent M γ) where
  pure := pureEvent

def applyEvent [Machine CTX M] ( ef : OrdinaryEvent M γ (α → β)) (ev : OrdinaryEvent M γ α) : OrdinaryEvent M γ β :=
  let event := ef.toEvent <*> ev.toEvent
  {
    guard := event.guard
    action := event.action
    safety := fun m x =>
    by
      simp [event, Seq.seq, apply_Event]
      intro Hinv ⟨Hgrd₁, _⟩
      have Hsafe₁ := ef.safety m x Hinv Hgrd₁
      apply ev.safety ; assumption

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
  let event := ev.toEvent >>= (fun x => (f x).toEvent)
  Event.toOrdinaryEvent
    event
   (fun m x => by
        simp [event, bind]
        intros Hinv Hgrd
        simp [bind_Event] at *
        obtain ⟨Hgrd₁, Hgrd₂'⟩ := Hgrd
        have Hgrd₂ := Hgrd₂' Hgrd₁
        simp at Hgrd₂
        have Hsafe₁ := ev.safety m x Hinv Hgrd₁
        apply (f (ev.action m x Hgrd₁).fst).safety ; assumption
   )

instance [Machine CTX M]: Monad (OrdinaryEvent M γ) where
  bind := bindEvent

theorem OrdinaryEvent_liftBind [Machine CTX M] (ev : OrdinaryEvent M γ α) (f : α → OrdinaryEvent M γ β):
  (ev >>= f).toEvent = (ev.toEvent >>= fun x => (f x).toEvent) :=
by
  exact rfl

instance [Machine CTX M]: LawfulMonad (OrdinaryEvent M γ) where
  bind_pure_comp := by
    intros
    apply OrdinaryEvent.ext
    apply bind_pure_comp

  bind_map := by simp [bind] ; intros ; rfl

  pure_bind := by
    intros α β x f
    apply OrdinaryEvent.ext
    rw[OrdinaryEvent_liftBind]
    apply LawfulMonad.pure_bind


  bind_assoc := by
    intros α β γ' x f g
    apply OrdinaryEvent.ext
    rw[OrdinaryEvent_liftBind]
    rw[OrdinaryEvent_liftBind]
    simp
    rw [← bind_assoc]
    simp
    rfl




/- Category and Arrow -/

instance [Machine CTX M]: Category (OrdinaryEvent M) where
  id := funEvent M id

  comp {α β γ} (ev₂ : OrdinaryEvent M β γ) (ev₁ : OrdinaryEvent M α β) : OrdinaryEvent M α γ :=
    let event := ev₁.toEvent (>>>) ev₂.toEvent
    {
      guard := event.guard
      action := event.action
      safety := fun m x => by
          simp [event]
          intro Hinv ⟨Hgrd₁, Hgrd₂'⟩
          have Hsafe₁ := ev₁.safety m x Hinv Hgrd₁
          apply ev₂.safety ; assumption
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
  let event := Arrow.first ev.toEvent
  {
    guard := event.guard
    action := event.action
    safety := fun m (x,_) =>
      by
        simp [Arrow.first, event]
        intros Hinv Hgrd
        apply ev.safety m x Hinv Hgrd

  }

instance [Machine CTX M]: Arrow (OrdinaryEvent M) where
  arrow {α β} (f : α → β) := Event.toOrdinaryEvent (Arrow.arrow f) (fun m x => by simp[Arrow.arrow])

  split {α α' β β'} (ev₁ : OrdinaryEvent M α β)  (ev₂ : OrdinaryEvent M α' β') : OrdinaryEvent M (α × α') (β × β') :=
  Event.toOrdinaryEvent
    (Arrow.split ev₁.toEvent ev₂.toEvent)
    (fun m (x, x') =>
      by
        simp [Arrow.split]
        intro Hinv ⟨Hgrd₁, _⟩
        apply ev₁.safety m x Hinv Hgrd₁)



theorem OrdinaryEvent_lift_arrow [Machine CTX M] (f : α → β):
  (instArrowOrdinaryEvent.arrow f).toEvent = (instArrowEvent (M:=M)).arrow f :=
by
  exact rfl

theorem OrdinaryEvent_lift_split [Machine CTX M] {α α' β β'} (ev₁ : OrdinaryEvent M α β) (ev₂ : OrdinaryEvent M α' β'):
  (instArrowOrdinaryEvent.split ev₁ ev₂).toEvent
  = (instArrowEvent (M:=M)).split ev₁.toEvent ev₂.toEvent :=
by
  exact rfl

theorem OrdinaryEvent_lift_first [Machine CTX M] {α β} (ev : OrdinaryEvent M α β):
  (instArrowOrdinaryEvent.first ev (γ:=γ)).toEvent
  = (instArrowEvent (M:=M)).first (ev.toEvent) :=
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


/- Arrow Choice -/

def altOrdinaryEvent [Machine CTX M] (evl : OrdinaryEvent M α β) (evr : OrdinaryEvent M γ δ)
  : OrdinaryEvent M (Sum α γ) (Sum β δ) :=
  {
    guard := fun m x => match x with
                        | .inl l => evl.guard m l
                        | .inr r => evr.guard m r
    action := fun m x grd => match x with
                        | .inl l => let (y, m') := evl.action m l grd
                                    (Sum.inl y, m')
                        | .inr r => let (y, m') := evr.action m r grd
                                    (Sum.inr y, m')
    safety := fun m x hinv grd =>
      by
        simp[Machine.invariant]
        cases x
        case inl val =>
          simp
          exact evl.safety m val hinv grd
        case inr val =>
          simp
          exact evr.safety m val hinv grd
  }

instance [Machine CTX M]: ArrowChoice (OrdinaryEvent M) where
  splitIn := altOrdinaryEvent




instance [Machine CTX M] : LawfulArrowChoice (OrdinaryEvent M) where
  left_arr f :=
    by
      apply OrdinaryEvent.ext'
      simp
      simp[ArrowChoice.left]
      simp[Arrow.arrow]
      simp[altOrdinaryEvent]
      intros m x
      constructor
      · cases x
        · simp
        · simp
      intro grd₁
      cases x
      · simp
      simp
  left_f_g f g :=
    by
      apply OrdinaryEvent.ext'
      simp[ArrowChoice.left,Arrow.arrow,altOrdinaryEvent]
      intros m x
      constructor
      · cases x
        simp
        simp
      intros grd₁ grd₂
      cases x
      · simp
      simp
  arr_inl f :=
    by
      simp[ArrowChoice.left,Arrow.arrow,altOrdinaryEvent]
  split f g :=
    by
      apply OrdinaryEvent.ext'
      simp[ArrowChoice.left,Arrow.arrow,ArrowChoice.splitIn,altOrdinaryEvent]
      intros m x
      constructor
      · cases x
        · simp
        · simp
      intros grd₁ grd₂
      cases x
      · simp
      simp
  assoc f :=
    by
      apply OrdinaryEvent.ext'
      simp[ArrowChoice.left,Arrow.arrow,altOrdinaryEvent,assocsum]
      intros m x
      constructor
      · cases x
        case a.left.inl val =>
          cases val
          · simp
          · simp
        · simp
      · intro grd₁
        cases x
        case a.right.inl val =>
          cases val
          · simp
          · simp
        · simp




/- Contravariant functor -/

abbrev CoEvent (M) [Machine CTX M] (α) (β) :=
   OrdinaryEvent M β α

@[simp]
def OrdinaryEvent_from_CoEvent [Machine CTX M] (ev : CoEvent M α β) : OrdinaryEvent M β α := ev

@[simp]
def CoEvent_from_OrdinaryEvent [Machine CTX M] (ev : OrdinaryEvent M α β) : CoEvent M β α := ev

/- Weirdly had to modify proofs compared to the previous version...-/

instance [Machine CTX M]: ContravariantFunctor (CoEvent M γ) where
  contramap {α β} (f : β → α) (ev : CoEvent M γ α) :=
  let event := let ev' := coEvent_from_Event ev.toEvent
             let ev'' := ContravariantFunctor.contramap f ev'
             Event_from_CoEvent ev''
  Event.toOrdinaryEvent
    event
    (fun m x =>
      by
        intros hinv hgrd
        exact ev.safety m (f x) hinv hgrd
    )


instance [Machine CTX M] : LawfullContravariantFunctor (CoEvent M α) where
  cmap_id _ := by rfl
  cmap_comp _ _ := by rfl

/- Profunctor -/
/- Weirdly had to modify proofs compared to the previous version...-/
instance [Machine CTX M] : Profunctor (OrdinaryEvent M) where
  dimap {α β} {γ δ} (f : β → α) (g : γ → δ) (ev : OrdinaryEvent M α γ) : OrdinaryEvent M β δ :=
    let event := Profunctor.dimap f g ev.toEvent
    Event.toOrdinaryEvent
      event

    (fun m x =>
      by
        intros Hinv Hgrd
        let ev' := OrdinaryEvent_from_CoEvent (ContravariantFunctor.contramap f (CoEvent_from_OrdinaryEvent ev))
        let ev'' := g <$> ev'
        have Hsafe := ev''.safety m x Hinv
        revert Hsafe ev' ev'' ; simp
        intro Hsafe
        exact Hsafe Hgrd
      )


instance [Machine CTX M] : LawfulProfunctor (OrdinaryEvent M) where
  dimap_id := rfl
  dimap_comp _ _ _ _ := rfl
/- Weirdly had to modify proofs compared to the previous version...-/

instance [Machine CTX M] : StrongProfunctor (OrdinaryEvent M) where
  first' {α β γ} (ev : OrdinaryEvent M α β): OrdinaryEvent M (α × γ) (β × γ) :=
    let event := StrongProfunctor.first' ev.toEvent
    Event.toOrdinaryEvent
      event
      (fun m x =>
        by
          intros Hinv Hgrd
          apply ev.safety <;> assumption
      )



instance [Machine CTX M] : LawfulStrongProfunctor (OrdinaryEvent M) where
