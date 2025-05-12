
import LeanMachines.NonDet.Ordinary
import LeanMachines.NonDet.Algebra.Basic

/-!
## Algebraic properties of non-deterministic events

The following instantiate various algebraic structures, complementing
the structural properties of the representation types (`_NDEvent`) with
more "lawful" properties for the main event type (`OrdinaryNDEvent`).

This part is rather experimental and is thus not fully documented yet.

-/

instance [Machine CTX M] : Functor (OrdinaryNDEvent M γ) where
  map {α β} (f : α → β) event :=
  let ev' : NDEvent M γ β := f <$> event.toNDEvent
  {
    guard := ev'.guard
    effect := ev'.effect
    safety := fun m z => by
      simp [ev', Functor.map]
      intros Hinv Hgrd y m' x Heff Hy
      exact event.safety m z Hinv Hgrd x m' Heff
    feasibility := fun m z => by
        simp [ev', Functor.map]
        intros Hinv Hgrd
        have Hfeas := event.feasibility m z Hinv Hgrd
        obtain ⟨y, m', Hfeas⟩ := Hfeas
        exists (f y)
        exists m'
        exists y
  }


instance [Machine CTX M] : LawfulFunctor (OrdinaryNDEvent M γ) where
  map_const := rfl
  id_map ev := by simp [Functor.map]

  comp_map g h ev := by
    simp [Functor.map]
    cases ev
    case mk _ev _safe _feas =>
      simp
      have Hcm := LawfulFunctor.comp_map g h _ev
      simp [Functor.map] at Hcm
      assumption

/- XXX:
--  The output contravariant functor not provable, because we would
-- need a iso morphisme between α and β.
instance [Machine CTX M] : ContravariantFunctor (OrdinaryNDEvent M γ) where
  contramap {α β} (f : β → α) event :=
  let ev' : _NDEvent M γ β := ContravariantFunctor.contramap f event.to_NDEvent
  {
    guard := ev'.guard
    effect := ev'.effect
    po := {
      safety := fun m x => by simp [ev', ContravariantFunctor.contramap]
                              intros Hinv Hgrd y m' Heff
                              apply event.po.safety m x Hinv Hgrd (f y) m' Heff
      feasibility := fun m x => by simp [ev', ContravariantFunctor.contramap]
                                   intros Hinv Hgrd
                                   have Hfeas := event.po.feasibility m x Hinv Hgrd
                                   obtain ⟨y, m', Hfeas⟩ := Hfeas



    }
  }
-/


-- The input contravariant functor
abbrev CoOrdinaryNDEvent (M) [Machine CTX M] (α) (β) := OrdinaryNDEvent M β α


@[simp]
def CoOrdinaryNDEvent_from_OrdinaryNDEvent [Machine CTX M] (ev : OrdinaryNDEvent M α β) : CoOrdinaryNDEvent M β α :=
 ev

@[simp]
def OrdinaryNDEvent_from_CoOrdinaryNDEvent [Machine CTX M] (ev : CoOrdinaryNDEvent M β α) : OrdinaryNDEvent M α β :=
 ev

instance [Machine CTX M] : ContravariantFunctor (CoOrdinaryNDEvent M γ) where
  contramap {α β} (f : β → α) event :=
  let ev : CoNDEvent M γ β := ContravariantFunctor.contramap f event.toNDEvent
  {
     guard := ev.guard
     effect := ev.effect
     safety := fun m x => by
        --simp
        revert ev
        cases event
        case mk _ev Hsafe _ =>
          simp [ContravariantFunctor.contramap]
          intros Hinv Hgrd y m' Heff
          apply Hsafe m (f x) Hinv Hgrd y m' Heff
     feasibility := fun m x => by
        --simp
        intro Hinv
        revert ev
        cases event
        case mk _ev _ Hfeas =>
          simp [ContravariantFunctor.contramap]
          apply Hfeas m (f x) Hinv
  }


instance [Machine CTX M] : LawfullContravariantFunctor (CoOrdinaryNDEvent M γ) where
  cmap_id _ := rfl
  cmap_comp _ _ := rfl

instance [Machine CTX M] : Profunctor (OrdinaryNDEvent M) where
  dimap {α β} {γ δ} (f : β → α) (g : γ → δ) (ev : OrdinaryNDEvent M α γ) : OrdinaryNDEvent M β δ :=
  let ev' := OrdinaryNDEvent_from_CoOrdinaryNDEvent (ContravariantFunctor.contramap f (CoOrdinaryNDEvent_from_OrdinaryNDEvent ev))
  g <$> ev'


instance [Machine CTX M] : LawfulProfunctor (OrdinaryNDEvent M) where
  dimap_id := by simp [Profunctor.dimap, ContravariantFunctor.contramap]
                 exact fun {α β} => rfl
  dimap_comp f f' g g' := by
    funext event
    have Hdc' := LawfulProfunctor.dimap_comp (pf:=NDEvent M) f f' g g'
    have Hdc : Profunctor.dimap (f' ∘ f) (g ∘ g') event.toNDEvent = (Profunctor.dimap f g ∘ Profunctor.dimap f' g') event.toNDEvent := by
      exact congrFun Hdc' event.toNDEvent
    cases event
    case _ ev safe feas =>
      simp at *
      simp [Profunctor.dimap, ContravariantFunctor.contramap, Functor.map] at *
      simp [*]

instance [Machine CTX M] : StrongProfunctor (OrdinaryNDEvent M) where
  first' {α β γ} (event : OrdinaryNDEvent M α β): OrdinaryNDEvent M (α × γ) (β × γ) :=
    let ev : NDEvent M (α × γ) (β × γ) := StrongProfunctor.first' event.toNDEvent
    {
      guard := ev.guard
      effect := ev.effect
      safety := fun m (x, z) => by
          simp [ev, StrongProfunctor.first']
          intros Hinv Hgrd
          have Hsafe := event.safety m x Hinv Hgrd
          intros y _ m' _ Heff
          exact Hsafe y m' Heff

      feasibility := fun m (x, z) => by
          simp [ev, StrongProfunctor.first']
          intro Hinv Hgrd
          have Hfeas := event.feasibility m x Hinv Hgrd
          obtain ⟨y, m', Hfeas⟩ := Hfeas
          exists y ; exists m'
    }


instance [Machine CTX M] : LawfulStrongProfunctor (OrdinaryNDEvent M) where
  dimap_pi_id :=
    by
      simp[Profunctor.dimap,Prod.fst,StrongProfunctor.first']
      simp[ContravariantFunctor.contramap,Functor.map]
  first_first :=
    by
      simp[Profunctor.dimap,Prod.fst,StrongProfunctor.first']
      simp[ContravariantFunctor.contramap,Functor.map]
      simp[α_,α_inv]
      intros α β γ γ' a
      funext m x grd (y,m')
      simp
      constructor
      · intro h
        exists y.1.1
        constructor
        · exact h.2.2
        · rw[←h.1]
          rw[←h.2.1]
      · intro h
        obtain ⟨w,⟨hw₁,hw₂⟩⟩ := h
        constructor
        · rw[hw₂]
        · constructor
          · rw[hw₂]
          · rw[hw₂]
            exact hw₁
  dinaturality :=
    by
      simp[Profunctor.dimap,StrongProfunctor.first']
      simp[ContravariantFunctor.contramap,Functor.map]
      intros α β γ δ a f
      funext m x grd (y,m')
      simp
      constructor
      · intro h
        exists y.1
        constructor
        · exact h.2
        · rw[←h.1]
      · intro h
        obtain ⟨w,⟨hw₁,hw₂⟩⟩ := h
        constructor
        · rw[hw₂]
        · rw[hw₂]
          exact hw₁

instance [Machine CTX M]: Category (OrdinaryNDEvent M) where
  id {α }:=
  let ev : NDEvent M α α := Category.id
  {
    guard := ev.guard
    effect := ev.effect
    safety := fun m x => by simp [ev]
    feasibility := fun m x => by simp [ev]
  }

  comp {α β γ} (ev₂ : OrdinaryNDEvent M β γ) (ev₁ : OrdinaryNDEvent M α β) : OrdinaryNDEvent M α γ :=
    let ev : NDEvent M α γ := Category.comp ev₂.toNDEvent ev₁.toNDEvent
    { guard := ev.guard
      effect := ev.effect
      safety := fun m x => by
          -- simp
          intros Hinv
          have Hsafe₁ := ev₁.safety m x Hinv
          have Hsafe₂ := ev₂.safety
          simp [ev] at *
          intro ⟨Hgrd₁,Hgrd₂'⟩ z m'' y m' Heff₁ Heff₂'
          have Hsafe₁ := Hsafe₁ Hgrd₁ y m' Heff₁
          have Hgrd₂ := Hgrd₂' Hgrd₁ y m' Heff₁
          have Heff₂ := Heff₂' Heff₁
          apply Hsafe₂ m' y Hsafe₁ <;> assumption

      feasibility := fun m x => by
          simp [ev]
          intro Hinv ⟨Hgrd₁,Hgrd₂'⟩
          have Hfeas₁ := ev₁.feasibility m x Hinv Hgrd₁
          obtain ⟨y, m', Heff₁⟩ := Hfeas₁
          have Hsafe₁ := ev₁.safety m x Hinv Hgrd₁ y m' Heff₁
          have Hgrd₂ := Hgrd₂' Hgrd₁ y m' Heff₁
          have Hfeas₂ := ev₂.feasibility m' y Hsafe₁ Hgrd₂
          obtain ⟨z, m'', Heff₂⟩ := Hfeas₂
          exists z ; exists m'' ; exists y ; exists m'
          simp [*]
      }


instance [Machine CTX M]: LawfulCategory (OrdinaryNDEvent M) where
  id_right ev := by
    simp
    have Hir := LawfulCategory.id_right ev.toNDEvent
    simp at Hir
    cases ev
    case mk _ po =>
      simp [Hir]

  id_left ev := by
    have Hil := LawfulCategory.id_left ev.toNDEvent
    simp at Hil
    cases ev
    case mk _ po =>
      simp [Hil]

  id_assoc ev₁ ev₂ ev₃ := by
    have Hia := LawfulCategory.id_assoc ev₁.toNDEvent ev₂.toNDEvent ev₃.toNDEvent
    simp [*] at *
    cases ev₁
    cases ev₂
    cases ev₃
    simp [Hia]

-- XXX: This axiom is required to obtain feasibility
/-
axiom OrdinaryNDEvent_split_feasibility_ax {CTX} {M} [Machine CTX M] [Semigroup M] {α β α' β'} (ev₁ : _NDEvent M α β)  (ev₂ : _NDEvent M α' β')
  (m : M) (x : α) (x' : α'):
  (∃ y, ∃ grd₁, ∃ m', ev₁.effect m x grd₁ (y, m'))
  → (∃ y', ∃ grd₂, ∃ m', ev₂.effect m x' grd₂ (y', m'))
  → (∃ y, ∃ y', ∃ m', (Arrow.split ev₁ ev₂).effect m (x, x') (by sorry) ((y, y'), m'))
-/

class ParallelMachine (M) [Machine CTX M] extends Semigroup M where
  par_safe (m₁ m₂ : M):
    Machine.invariant m₁
    → Machine.invariant m₂
    → Machine.invariant (m₁ * m₂)

instance [Machine CTX M] [ParallelMachine M]: Arrow (OrdinaryNDEvent M) where

  arrow {α β} (f : α → β) :=
    let event : NDEvent M α β := Arrow.arrow f
    {
      guard := event.guard
      effect := event.effect
      safety := fun m x => by simp [event, Arrow.arrow]
      feasibility := fun m x => by simp [event, Arrow.arrow]
    }

  split {α α' β β'} (ev₁ : OrdinaryNDEvent M α β)  (ev₂ : OrdinaryNDEvent M α' β') : OrdinaryNDEvent M (α × α') (β × β') :=
    let event : NDEvent M  (α × α') (β × β') := Arrow.split ev₁.toNDEvent ev₂.toNDEvent
    {
      guard := event.guard
      effect := event.effect
      safety := fun m (x₁,x₂) => by
          simp [event, Arrow.split]
          intro Hinv ⟨Hgrd₁, Hgrd₂⟩ y₁ y₂ m' m'₁ Heff₁ m'₂ Heff₂ Hm'
          have Hsafe₁ := ev₁.safety m x₁ Hinv Hgrd₁ y₁ m'₁ Heff₁
          have Hsafe₂ := ev₂.safety m x₂ Hinv Hgrd₂ y₂ m'₂ Heff₂
          rw [Hm']
          apply ParallelMachine.par_safe m'₁ m'₂ <;> assumption

      -- this could be called "weak feasibility"
      feasibility := fun m (x₁, x₂) => by
          simp [Arrow.split, event]
          intro Hinv ⟨Hgrd₁, Hgrd₂⟩
          have Hfeas₁ := ev₁.feasibility m x₁ Hinv Hgrd₁
          have Hfeas₂ := ev₂.feasibility m x₂ Hinv Hgrd₂
          obtain ⟨y₁, m'₁, Hfeas₁⟩ := Hfeas₁
          obtain ⟨y₂, m'₂, Hfeas₂⟩ := Hfeas₂
          exists y₁ ; exists y₂
          exists (m'₁ * m'₂)
          exists m'₁
          constructor
          · assumption
          exists m'₂
      }


  -- XXX : once again, an explicit `first` must be defined because `first-from-split` does
  --       not satisfy the `arrow_unit` law
  first {α β γ : Type} (ev : OrdinaryNDEvent M α β) : OrdinaryNDEvent M (α × γ) (β × γ) :=
  let event : NDEvent M (α × γ) (β × γ) := Arrow.first ev.toNDEvent
  {
    guard := event.guard
    effect := event.effect
    safety := fun m (x,y) => by
        simp [event, Arrow.first]
        intros Hinv Hgrd
        intros u _ m' Heff _
        apply ev.safety m x Hinv Hgrd u m' Heff

    feasibility := fun m (x,y) => by
        simp [event, Arrow.first]
        intros Hinv Hgrd
        have Hfeas := ev.feasibility m x Hinv Hgrd
        obtain ⟨y',m', Heff⟩ := Hfeas
        exists y' ; exists m'

  }



instance [Machine CTX M] [ParallelMachine M]: LawfulArrow (OrdinaryNDEvent M) where
  arrow_id := by simp [Arrow.arrow]

  arrow_ext {α β γ } f :=
      by simp [Arrow.arrow, Arrow.first, Arrow.split]
         funext m (x₁, x₂) grd ((y₁, y₂), m')
         simp
         constructor <;> (intros ; simp [*])

  arrow_fun f g := by
    simp [Arrow.arrow]
    have Hfun := LawfulArrow.arrow_fun (arr := NDEvent M) f g
    simp [Arrow.arrow] at Hfun
    simp [Hfun]

  arrow_xcg ev g := by
    apply OrdinaryNDEvent.ext
    apply LawfulArrow.arrow_xcg

  arrow_unit ev := by
    apply OrdinaryNDEvent.ext
    apply LawfulArrow.arrow_unit

  arrow_assoc {α β γ δ} ev := by
    simp [Arrow.arrow, Arrow.first]
    have Hasc := @LawfulArrow.arrow_assoc (arr:=NDEvent M) _ _ α β γ δ ev.toNDEvent
    simp [Arrow.arrow, Arrow.first] at Hasc
    simp [Hasc]
