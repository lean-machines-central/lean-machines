
import LeanMachines.NonDet.Basic

/-!
# Algebraic properties of non-deterministic events
(experimental, for now undocumented)
-/


-- Remark: The functor instance is existential, not surprising given the relational context
instance [Machine CTX M] : Functor (NDEvent M γ) where
  map f ev :=
  {
    guard := ev.guard
    effect := fun m x grd (y, m') => ∃ z, ∃ m'', ev.effect m x grd (z, m'')
                                                 ∧ y = f z ∧ m' = m''
  }

instance [Machine CTX M] : LawfulFunctor (NDEvent M γ) where
  map_const := rfl
  id_map ev := by simp [Functor.map]

  comp_map g h ev := by
    simp [Functor.map]
    funext m x grd (y,m')
    apply propext
    constructor
    · intro Hz
      cases Hz
      case _ z H =>
        simp at H
        simp
        exists (g z)
        constructor
        · exists z
          simp [H]
        simp [H]
    simp
    intros z t Heff Heq₁ Heq₂
    exists t
    simp [Heff, Heq₁, Heq₂]


-- There are two possible, distinct ContravariantFunctor functors
-- for non-deterministic events.

-- The first operates on the output, hence it cannot be use
-- in a profunctor context
instance [Machine CTX M] : ContravariantFunctor (NDEvent M γ) where
  contramap f ev :=
  {
    guard := ev.guard
    effect := fun m x grd (y, m') => ev.effect m x grd ((f y), m')
  }

instance [Machine CTX M] : LawfullContravariantFunctor (NDEvent M β) where
  cmap_id _ := rfl
  cmap_comp _ _ := rfl

-- The second operates on the input
abbrev CoNDEvent (M) [Machine CTX M] (α) (β) := NDEvent M β α

instance [Machine CTX M]: Coe (NDEvent M α β) (CoNDEvent M β α) where
  coe ev := ev

instance [Machine CTX M]: Coe (CoNDEvent M β α) (NDEvent M α β) where
  coe ev := ev

instance [Machine CTX M] : ContravariantFunctor (CoNDEvent M γ) where
  contramap f ev :=
  {
     guard := fun m x => ev.guard m (f x)
     effect := fun m x grd (y, m')  => ev.effect m (f x) grd (y, m')
  }

instance [Machine CTX M] : LawfullContravariantFunctor (CoNDEvent M γ) where
  cmap_id _ := rfl
  cmap_comp _ _ := rfl

-- There is a unique possible profunctor instance
instance [Machine CTX M] : Profunctor (NDEvent M) where
  dimap {α β} {γ δ} (f : β → α) (g : γ → δ) (ev : NDEvent M α γ) : NDEvent M β δ :=
  let ev' : CoNDEvent M γ β := ContravariantFunctor.contramap f ev
  g <$> ev'

instance [Machine CTX M] : LawfulProfunctor (NDEvent M) where
  dimap_id := by simp [Profunctor.dimap, ContravariantFunctor.contramap]
                 exact fun {α β} => rfl
  dimap_comp f f' g g' := by
    simp [Profunctor.dimap, ContravariantFunctor.contramap, Functor.map]
    funext ev
    simp
    funext m x grd (y,m')
    simp
    constructor
    · intro Heff
      cases Heff
      case _ u Heff =>
        exists (g' u)
        simp [Heff]
        exists u
        simp [Heff]
    intro Heff
    cases Heff
    case _ t Heff =>
      simp at Heff
      cases Heff
      case _ Heff Hy =>
        cases Heff
        case _ u Heff =>
          exists u
          simp [Heff, Hy]

instance [Machine CTX M] : StrongProfunctor (NDEvent M) where
  first' {α β γ} (ev : NDEvent M α β): NDEvent M (α × γ) (β × γ) :=
    {
      guard := fun m (x, _) => ev.guard m x
      effect := fun m (x,u) grd ((y, v), m') => v = u ∧ ev.effect m x grd (y, m')
    }

instance [Machine CTX M] : LawfulStrongProfunctor (NDEvent M) where
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
      refine funext ?_
      intro m
      refine funext ?_
      intro x
      refine funext ?_
      intro grd
      refine funext ?_
      intro (y,m')
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
      refine funext ?_
      intro m
      refine funext ?_
      intro x
      refine funext ?_
      intro grd
      refine funext ?_
      intro (y,m')
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


instance [Machine CTX M]: Category (NDEvent M) where
  id := {
    guard _ _ := True
    effect := fun m x _ (y, m') => y = x ∧ m' = m
  }

  comp {α β γ} (ev₂ : NDEvent M β γ) (ev₁ : NDEvent M α β) : NDEvent M α γ :=
    { guard := fun m x => ev₁.guard m x
                          ∧ ((grd : ev₁.guard m x)
                             → (∀ y, ∀ m', ev₁.effect m x grd (y, m')
                                → ev₂.guard m' y))
      effect := fun m x grd (z, m'') =>
        ∃ y m',  ev₁.effect m x grd.1 (y, m') ∧
                 ((eff₁ : ev₁.effect m x grd.1 (y, m')) →
                  ev₂.effect m' y (grd.2 grd.1 y m' eff₁) (z, m''))
    }

theorem LawfulCategory_assoc_guard [Machine CTX M] (ev₁ : NDEvent M γ δ) (ev₂ : NDEvent M β γ) (ev₃ : NDEvent M α β):
  (ev₁ (<<<) ev₂ (<<<) ev₃).guard = ((ev₁ (<<<) ev₂) (<<<) ev₃).guard :=
by
  simp
  funext m x
  simp
  constructor
  · simp
    intro Hgrd₃
    intro Hgrd₂''
    have Hgrd₂' := Hgrd₂'' Hgrd₃ ; clear Hgrd₂''
    intro H'
    simp [Hgrd₃] at *
    intros y m' Heff₃
    have H := H' Hgrd₂' ; clear H'
    have Hgrd₂ := Hgrd₂' y m' Heff₃
    simp [Hgrd₂]
    intros z mm'
    intro Heff₂
    have Hgrd₁'' := H z mm' y m' Heff₃
    apply Hgrd₁''
    intro Heff₃'
    assumption
  · simp
    intro Hgrd₃
    intro Hgrd₁'''
    have Hgrd₁'' := Hgrd₁''' Hgrd₃ ; clear Hgrd₁'''
    simp [Hgrd₃]
    constructor
    · intros y m' Heff₃
      obtain ⟨Hgrd₂, Hgrd₁'⟩ := Hgrd₁'' y m' Heff₃ ; clear Hgrd₁''
      assumption
    · intros H z mm' y m' Heff₃ Heff₂'
      have Hgrd₁' := Hgrd₁'' y m' Heff₃ ; clear Hgrd₁''
      have Heff₂ := Heff₂' Heff₃ ; clear Heff₂'
      have Hgrd₂ := H y m' Heff₃
      simp [Hgrd₂] at Hgrd₁'
      exact Hgrd₁' z mm' Heff₂

set_option maxHeartbeats 300000

instance [Machine CTX M]: LawfulCategory (NDEvent M) where
  id_right ev := by
    apply NDEvent.ext'
    simp

  id_left ev := by
    apply NDEvent.ext'
    simp
    intros m x y m' grd₁ grd₂
    constructor
    · intro ⟨yy,⟨mm',H₁,H₂'⟩⟩
      have H₂ := H₂' H₁
      simp [H₁,H₂]
    · intro Heff₁
      exists y
      exists m'
      simp [Heff₁]

  id_assoc ev₁ ev₂ ev₃ := by
    apply NDEvent.ext
    case guard =>
      exact LawfulCategory_assoc_guard ev₁ ev₂ ev₃

    case effect =>
      apply _Effect_ext_ax
      intros m x
      constructor
      · rw [@LawfulCategory_assoc_guard]
      · intros y m' grd₁ grd₂
        simp
        constructor
        · intro H
          obtain ⟨z, m'', ⟨⟨yy, mm', ⟨Heff₃, H₁⟩⟩, H₂⟩⟩ := H
          have Heff₂ := H₁ Heff₃
          exists yy ; exists mm'
          simp [Heff₃] at *
          exists z ; exists m''
          simp [Heff₂]
          have Heff₁' := H₂ yy mm'
          apply Heff₁'
          constructor
          · assumption
          · intro Heff₃_bis
            assumption
        · intro ⟨yy, mm', ⟨Heff₃,H⟩⟩
          obtain ⟨z, m'', ⟨Heff₂, Heff₁'⟩⟩ := H Heff₃
          exists z ; exists m''
          constructor
          · exists yy ; exists mm'
            simp [Heff₂, Heff₃]
          · intros yyy mmm' H
            exact Heff₁' Heff₂
    -- QED  (a big one!)


@[simp]
def arrow_NDEvent (M) [Machine CTX M] (f : α → β) : NDEvent M α β :=
  {
    guard := fun _ _ => True
    effect := fun m x _ (y, m') => y = f x ∧ m' = m
  }

-- Split is simply parallel composition
@[simp]
def split_NDEvent [Machine CTX M] (ev₁ : NDEvent M α β) (ev₂ : NDEvent M γ δ) : NDEvent M (α × γ) (β × δ) :=
  {
    guard := fun m (x, y) => ev₁.guard m x ∧ ev₂.guard m y
    effect := fun m (x, y) grd ((x', y'), m') => ev₁.effect m x grd.1 (x', m') ∧ ev₂.effect m y grd.2 (y', m')
  }

-- Remark: without an explicit first the law `arrow_unit` is not provable
@[simp]
def first_NDEvent [Machine CTX M] (ev : NDEvent M α β) : NDEvent M (α × γ) (β × γ) :=
  {
    guard := fun m (x, _) => ev.guard m x
    effect := fun m (x, y) grd ((x', y'), m') => ev.effect m x grd (x', m') ∧ y'= y
  }

-- An alternative possible definition for split based on first

@[simp]
def split_NDEvent_fromFirst [Machine CTX M] (ev₁ : NDEvent M α β) (ev₂ : NDEvent M γ δ) : NDEvent M (α × γ) (β × δ) :=
  Arrow.split_from_first (arrow_NDEvent M (fun (x, y) => (y, x)))
                         first_NDEvent ev₁ ev₂

/-
instance [Machine CTX M]: Arrow (_NDEvent M) where
  arrow := arrow_NDEvent M
  split := split_NDEvent
  first := first_NDEvent
-/

-- a more direct definition
instance [Machine CTX M] [Semigroup M]: Arrow (NDEvent M) where
  arrow {α β} (f : α → β) : NDEvent M α β := {
    guard := fun _ _ => True
    effect := fun m x _ (y, m') => y = f x ∧ m' = m
  }

  split {α α' β β'} (ev₁ : NDEvent M α β) (ev₂ : NDEvent M α' β') : NDEvent M (α × α') (β × β') := {
    guard := fun m (x,y) => ev₁.guard m x ∧ ev₂.guard m y
    effect := fun m (x, y) grd ((x', y'), m') =>
                ∃ m'₁ m'₂, ev₁.effect m x grd.1 (x', m'₁) ∧ ev₂.effect m y grd.2 (y', m'₂) ∧ m' = m'₁ * m'₂
  }
  first := first_NDEvent

instance [Machine CTX M] [Semigroup M]: LawfulArrow (NDEvent M) where
  arrow_id := by simp [Arrow.arrow]
  arrow_ext f := by
    simp [Arrow.arrow, Arrow.first]
    funext m (x, z) grd ((y, z'), m')
    simp
    constructor
    <;> (intro H ; simp [H])

  arrow_fun f g := by
    apply NDEvent.ext'
    simp [Arrow.arrow]

  arrow_xcg ev g := by
    apply NDEvent.ext'
    simp [Arrow.arrow, Arrow.first]
    intros m x y yy xx m' grd₁ grd₂
    constructor
    · intro ⟨Heff, Hg⟩
      exists yy ; exists y ; exists m'
      simp [Heff, Hg]
    · simp
      intros z₁ z₂ mm' Heff Hz₂
      simp [Heff, Hz₂]
      intros H₁ H₂ H₃
      simp [*]

  arrow_unit ev := by
    apply NDEvent.ext'
    intro m (x, x')
    simp [Arrow.arrow, Arrow.first]
    intros y m' Hgrd Hgrd'
    constructor
    case a.mp =>
      intro ⟨y₁, y₂, mm, ⟨H', H⟩⟩
      simp [H'] at H
      simp [*]
    case a.mpr =>
      intro Heff
      exists y ; exists x' ; exists m'
      simp [Heff]

  arrow_assoc ev := by
    apply NDEvent.ext'
    intro m ((x, z), t)
    simp [Arrow.first, Arrow.arrow]
    intros y zz tt m' grd₁ grd₂
    constructor
    case a.mp =>
      intro ⟨yy,zzz,ttt,mm',⟨H₁,H₂⟩⟩
      simp [H₁, H₂]
    case a.mpr =>
      intro ⟨Heff, Hzz, Htt⟩
      exists y ; exists z ; exists t ; exists m'
      simp [*]

/-  ArrowChoice -/

def altNDEvent [Machine CTX M] (evl : NDEvent M α β) (evr : NDEvent M γ δ)
  : NDEvent M (Sum α γ) (Sum β δ) :=
  {
    guard := fun m x => match x with
                        | .inl l => evl.guard m l
                        | .inr r => evr.guard m r
    effect := fun m x grd (y,m') =>
       match x with
       | .inl xl => ∀ yl, evl.effect m xl grd (yl, m')
                          → y = Sum.inl yl
       | .inr xr => ∀ yr, evr.effect m xr grd (yr, m')
                          → y = Sum.inr yr
  }

instance [Machine CTX M] [Semigroup M]: ArrowChoice (NDEvent M) where
  splitIn := altNDEvent


/-  Conjoin events -/

def conj_NDEvent [Machine CTX M] (ev₁ : NDEvent M α β) (ev₂ : NDEvent M α β)
  : NDEvent M α β :=
  {
    guard := fun m x => ev₁.guard m x ∨ ev₂.guard m x
    effect := fun m x _ (y, m') =>
      ((grd₁ : ev₁.guard m x) → ev₁.effect m x grd₁ (y, m'))
      ∧ ((grd₂ : ev₂.guard m x) → ev₂.effect m x grd₂ (y, m'))
  }

instance [Machine CTX M] [Semigroup M]: ArrowPlus (NDEvent M) where
  zero := skip_NDEvent
  conjoin := conj_NDEvent
