
import LeanMachines.Event.Prelude
import LeanMachines.Event.Basic
import LeanMachines.Algebra.Contravariant
import LeanMachines.Algebra.Profunctor
import LeanMachines.Algebra.Arrow
import Mathlib.Algebra.Group.Defs


/-!
## Algebraic properties of _Events

The following instantiate various algebraic structures
for the representation type of deterministic _Events: `_Event`.

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
    guard := fun _ _ => True
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

abbrev _K_Event M [Machine CTX M] γ := Kleisli (_Event M γ)
  -- α → (_Event M γ) β

--def instArrowK_Event [Machine CTX M]: Arrow (_K_Event M γ) := inferInstance

/-
variable (f : α → β)
variable (M)
variable (instM : Machine CTX M)
variable (γ)
#check (Arrow.arrow f : _K_Event M γ α β)
-/

-- Arrows are in a way less powerful (but more general) than Monads
-- but _Events are monads only considering their output type
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

instance [Machine CTX M]: Arrow (_Event M) where
  arrow {α β} (f : α → β) := {
    guard := fun _ _ => True
    action := fun m x _ => (f x, m)
  }

  split {α α' β β'} (ev₁ : _Event M α β)  (ev₂ : _Event M α' β') : _Event M (α × α') (β × β') := {
    guard := fun m (x, y) => ev₁.guard m x ∧ ev₂.guard m y
    action := fun m (x, y) grd => let (x',m'₁) := ev₁.action m x grd.1
                              let (y', _) := ev₂.action m y grd.2
                              -- note : we forget the second state change
                              ((x', y'), m'₁)
  }
instance [Machine CTX M]  : LawfulArrow (_Event M) where
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
  arrow_unit ev := by
    apply _Event.ext'
    simp [Arrow.arrow, Arrow.first]

  arrow_assoc {α β γ δ} (f : _Event M α β) := by
    apply _Event.ext'
    simp [Arrow.arrow, Arrow.first]




class CustomCompo (M : Type u) where
  comp : M → M → M → M
class LawfulCustomCompo (M : Type u) extends CustomCompo M where
  assoc : ∀ a b c d : M, comp d a (comp d b c) = comp d (comp d a b ) c
  idem : ∀ m d : M, comp d m m = m
  modif (d : M) : ∀ m : M,  comp d m d = m
-- more explicit alternative

instance customCompo [Machine CTX M] [LawfulCustomCompo M]: Arrow (_Event M) where
  arrow {α β} (f : α → β) := {
    guard := fun _ _ => True
    action := fun m x _ => (f x, m)
  }

  split {α α' β β'} (ev₁ : _Event M α β)  (ev₂ : _Event M α' β') : _Event M (α × α') (β × β') := {
    guard := fun m (x, y) => ev₁.guard m x ∧ ev₂.guard m y
    action := fun m (x, y) grd => let (x',m'₁) := ev₁.action m x grd.1
                              let (y', m'₂) := ev₂.action m y grd.2
                              -- note : we forget the second state change
                              ((x', y'), CustomCompo.comp m m'₁ m'₂)
  }




instance [Machine CTX M] [LawfulCustomCompo M] : LawfulArrow (_Event M) where
  arrow_id := by simp [Arrow.arrow]
  arrow_ext _ := by
    apply _Event.ext'
    simp [Arrow.arrow, Arrow.first]
    intros m' a b
    exact LawfulCustomCompo.idem m' m'
  arrow_fun _ _ := by
    apply _Event.ext'
    simp [Arrow.arrow, Arrow.first]
  arrow_xcg _ _ := by
    apply _Event.ext'
    simp [Arrow.arrow, Arrow.first]
  arrow_unit ev := by
    apply _Event.ext'
    simp [Arrow.arrow, Arrow.first]
    intros m a b grd₁ grd₂

    have h := LawfulCustomCompo.modif m (ev.action m a grd₁).2
    rw[h]
  arrow_assoc {α β γ δ} (f : _Event M α β) := by
    apply _Event.ext'
    simp [Arrow.arrow, Arrow.first]
    intros m a b d grd₁ grd₂
    have h := LawfulCustomCompo.modif m (f.action m a grd₁).2
    rw[h]
    assumption

/-  ArrowChoice -/

def alt_Event [Machine CTX M] (evl : _Event M α β) (evr : _Event M γ δ)
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

instance [Machine CTX M] [LawfulCustomCompo M]: ArrowChoice (_Event M) where
  splitIn := alt_Event


instance [Machine CTX M] [LawfulCustomCompo M]: LawfulArrowChoice (_Event M) where
  left_arr f :=
    by
      apply _Event.ext'
      simp
      simp[ArrowChoice.left]
      simp[Arrow.arrow]
      simp[alt_Event]
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
      apply _Event.ext'
      simp[ArrowChoice.left,Arrow.arrow,alt_Event]
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
      apply _Event.ext'
      simp[ArrowChoice.left,Arrow.arrow,alt_Event]
  split f g :=
    by
      apply _Event.ext'
      simp[ArrowChoice.left,Arrow.arrow,ArrowChoice.splitIn,alt_Event]
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
      apply _Event.ext'
      simp[ArrowChoice.left,Arrow.arrow,alt_Event,assocsum]
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


/- ContravariantFunctor functor -/

abbrev _Co_Event (M) [Machine CTX M] (α) (β) :=
  _Event M β α

@[simp]
def coEvent_from_Event [Machine CTX M] (ev : _Event M α β) : _Co_Event M β α :=
 ev

@[simp]
def Event_from_CoEvent [Machine CTX M] (ev : _Co_Event M β α) : _Event M α β :=
 ev

instance [Machine CTX M] : ContravariantFunctor (_Co_Event M γ) where
  contramap f ev := {
    guard := fun m x => ev.guard m (f x)
    action := fun m x => ev.action m (f x)
  }

instance [Machine CTX M] : LawfullContravariantFunctor (_Co_Event M β) where
  cmap_id _ := rfl
  cmap_comp _ _ := rfl

/- Profunctor -/

-- An indirect definition using the covariant and contravariant functors
--instance [Machine CTX M] : Profunctor (_Event M) where
--  dimap {α β} {γ δ} (f : β → α) (g : γ → δ) (ev : _Event M α γ) : _Event M β δ :=
--    let ev' := _Event_from_Co_Event (ContravariantFunctor.contramap f (co_Event_from_Event ev))
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
  dimap_pi_id a :=
  by
    simp[Profunctor.dimap,StrongProfunctor.first']
  first_first a :=
  by
    simp[Profunctor.dimap,StrongProfunctor.first',α_,α_inv]
  dinaturality a f :=
  by
    simp[Profunctor.dimap,StrongProfunctor.first']
