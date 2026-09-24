
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
    simp only [Functor.map, ↓existsAndEq, Function.comp_apply, and_true]


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
    simp only [Function.comp_apply, ↓existsAndEq, and_true]

instance [Machine CTX M] : StrongProfunctor (NDEvent M) where
  first' {α β γ} (ev : NDEvent M α β): NDEvent M (α × γ) (β × γ) :=
    {
      guard := fun m (x, _) => ev.guard m x
      effect := fun m (x,u) grd ((y, v), m') => v = u ∧ ev.effect m x grd (y, m')
    }

instance [Machine CTX M] : LawfulStrongProfunctor (NDEvent M) where
  dimap_pi_id :=
    by
      simp [Profunctor.dimap, StrongProfunctor.first']
      simp [ContravariantFunctor.contramap,Functor.map]
  first_first :=
    by
      simp only [Profunctor.dimap, StrongProfunctor.first',ContravariantFunctor.contramap,
        Functor.map,α_, ↓existsAndEq, α_inv, and_true, Prod.exists, Prod.mk.injEq, true_and,
        NDEvent.mk.injEq, heq_eq_eq]
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
    intro Hgrd₃ Hgrd₂''
    have Hgrd₂' := Hgrd₂'' Hgrd₃ ; clear Hgrd₂''
    intro H'
    simp [Hgrd₃] at *
    intros y m' Heff₃
    have H := H' Hgrd₂' ; clear H'
    have Hgrd₂ := Hgrd₂' y m' Heff₃
    simp [Hgrd₂]
    intros z mm' Heff₂
    have Hgrd₁'' := H z mm' y m' Heff₃
    apply Hgrd₁''
    intro Heff₃'
    assumption
  · simp
    intro Hgrd₃ Hgrd₁'''
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
    simp only [Category.comp, Category.id, Prod.mk.eta, implies_true, and_true,
      Subsingleton.forall₂_iff, true_and]
    intros m x y m' hgrd
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
          simp only [Heff₂, forall_true_left, true_and]
          have Heff₁' := H₂ yy mm'
          apply Heff₁'
          · exact Heff₃
          · intro _
            exact Heff₂
        · intro ⟨yy, mm', ⟨Heff₃,H⟩⟩
          obtain ⟨z, m'', ⟨Heff₂, Heff₁'⟩⟩ := H Heff₃
          exists z ; exists m''
          constructor
          · exists yy ; exists mm'
            simp [Heff₂, Heff₃]
          · intros yyy mmm' _ _
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
                ∃ m'₁ m'₂,
                ev₁.effect m x grd.1 (x', m'₁)
                ∧ ev₂.effect m y grd.2 (y', m'₂)
                ∧ m' = m'₁ * m'₂
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
    simp only [Category.rcomp, Category.comp, Arrow.arrow, fun_split, id_eq, Arrow.first,
      first_NDEvent, Prod.mk.eta, forall_and_index, ↓existsAndEq, and_true, forall_true_left,
      exists_eq_left, forall_eq_apply_imp_iff, forall_eq, forall_const, true_and,
      Prod.exists, implies_true, Subsingleton.forall₂_iff, Prod.forall, Prod.mk.injEq]
    intros m x y yy xx m' grd₁
    constructor
    · intro ⟨Heff,Hg⟩
      exists yy ; exists m'
      simp only [Heff,Hg,and_self, imp_self]
    · intro ⟨yyy,⟨mm',⟨Heff,Heqs⟩⟩⟩
      have Heqs' := Heqs Heff
      rw[←Heqs'.1.1,← Heqs'.2] at Heff
      exact ⟨Heff,Heqs'.1.2⟩


  arrow_unit ev := by
    apply NDEvent.ext'
    intro m (x, x')
    simp [Arrow.arrow, Arrow.first]
    intros y m' Hgrd
    constructor
    · intro ⟨yy,⟨mm,⟨Heff, Heqs⟩⟩⟩
      specialize Heqs Heff
      rw[Heqs.1,Heqs.2]
      exact Heff
    · intro Heff
      exists y ; exists m'
      simp only [Heff]
      simp only [and_self, imp_self]


  arrow_assoc ev := by
    apply NDEvent.ext'
    intro m ((x, z), t)
    simp [Arrow.first, Arrow.arrow]
    intros y zz tt m' grd
    constructor
    · intro ⟨yy,mm,Heff,Heqs⟩
      specialize Heqs Heff
      simp only[Heqs,Heff,and_self]
    · intro ⟨Heff,Hzz,Htt⟩
      exists y ; exists m'
      simp only [Heff,Hzz,Htt,and_self,imp_self]


/-  ArrowChoice -/



def altNDEvent [Machine CTX M] (evl : NDEvent M α β) (evr : NDEvent M γ δ)
  : NDEvent M (Sum α γ) (Sum β δ) :=
  {
    guard := fun m x => match x with
                        | .inl l => evl.guard m l
                        | .inr r => evr.guard m r
    effect := fun m x grd (y,m') =>
       match x with
       | .inl xl => ∃ yl, evl.effect m xl grd (yl, m')
                          ∧  y = Sum.inl yl
       | .inr xr => ∃ yr, evr.effect m xr grd (yr, m')
                          ∧  y = Sum.inr yr
  }

instance [Machine CTX M] [Semigroup M]: ArrowChoice (NDEvent M) where
  splitIn := altNDEvent

instance [Machine CTX M] [Semigroup M] : LawfulArrowChoice (NDEvent M) where
  left_arr {α β γ} (f : α → β):=
  by
    apply NDEvent.ext'
    simp only [ArrowChoice.left,Arrow.arrow,altNDEvent]
    intros m x
    constructor
    · simp
      cases x
      repeat trivial
    · simp
      constructor
      · intros y m' hgrd₁
        cases x
        case right.left.inl l =>
          simp
          constructor
          · intro hyp
            exact id (And.symm hyp)
          · intro hyp
            exact id (And.symm hyp)
        case right.left.inr r =>
          simp
      · intros z m' grd₁
        cases x
        case right.right.inl l =>
          simp
        case right.right.inr r =>
          simp
          exact And.comm

  left_f_g {α β γ ω} (f : NDEvent M α β) (g : NDEvent M β γ) :=
  by
    apply NDEvent.ext'
    simp only [ArrowChoice.left,Category.id,altNDEvent]
    intros m x
    cases x
    case inl l =>
      simp
    case inr r =>
      simp
  arr_inl {α β γ} (f : NDEvent M α β):=
  by
    apply NDEvent.ext'
    simp only [Arrow.arrow,ArrowChoice.left,altNDEvent]
    simp only [Category.rcomp, Category.comp, implies_true, and_true, Category.id, ↓existsAndEq,
      true_and, forall_and_index, forall_true_left, exists_eq_left,
      forall_eq_apply_imp_iff, forall_eq, forall_const, Subsingleton.forall₂_iff, Sum.forall,
      Sum.inl.injEq, exists_eq_right', reduceCtorEq, false_and, imp_false, and_not_self,
      exists_const, exists_false, and_false]
    intros m x y m' grd₁
    constructor
    · intro h
      have ⟨y',m'',heff⟩ := h
      rw[←(heff.2 heff.1).2] at heff
      rw[←(heff.2 heff.1).1] at heff
      exact heff.1
    · intro h
      exists y
      exists m'
      apply And.intro h
      intro _
      apply And.intro rfl rfl

  split {α β α' β'} (f : NDEvent M α β)  (g : α' → β') :=
  by
    apply NDEvent.ext'
    simp only [Arrow.arrow,ArrowChoice.left,ArrowChoice.splitIn,altNDEvent]
    intros m x
    simp
    cases x
    case inl l =>
      simp
      intros a m' grd₁
      constructor
      · intro h
        have ⟨y',m'',heff⟩ := h
        rw[←(heff.2 heff.1).2] at heff
        rw[←(heff.2 heff.1).1] at heff
        exact heff.1
      · intro h
        exists a
        exists m'
        apply And.intro h
        intro _
        apply And.intro rfl rfl
    case inr r =>
      simp
      intros a m'
      constructor
      · intro h
        exact And.symm h
      · intro h
        exact And.symm h
  assoc {α β γ δ} (f : NDEvent M α β) :=
  by
    apply NDEvent.ext'
    simp only [Arrow.arrow,ArrowChoice.left,altNDEvent]
    simp only [assocsum]
    intros m x
    cases x
    case inl l =>
      cases l
      case inl l' =>
        simp
        intros y m' grd₁
        constructor
        · intro h
          cases h
          case mp.intro y' mheff =>
            cases mheff
            case intro m' heff =>
              rw[←(heff.2 heff.1).2] at heff
              rw[←(heff.2 heff.1).1] at heff
              exact heff.1
        · intro h
          exists y
          exists m'
          apply And.intro h
          intro _
          apply And.intro rfl rfl
      case inr r' =>
        simp only [Category.rcomp, Category.comp, Category.id, ↓existsAndEq, true_and, Sum.exists,
          Sum.inl.injEq, exists_eq_right', reduceCtorEq, and_false, exists_false, Sum.inr.injEq,
          or_false, false_or, or_self, implies_true, and_true, forall_and_index, forall_true_left,
          exists_eq_left, forall_eq_apply_imp_iff, forall_eq, forall_const,
          IsEmpty.forall_iff, false_and, Sum.forall]
        intros a m'
        constructor
        · intro ⟨heq₁,heq₂⟩
          rw[heq₁,heq₂]
          exact And.intro rfl rfl
        · intro ⟨heq₁,heq₂⟩
          rw[heq₁,heq₂]
          exact And.intro rfl rfl
    case inr r =>
      simp only [Category.id]
      constructor
      · simp only [Category.rcomp, Category.comp, ↓existsAndEq, true_and, Sum.exists,
        Sum.inl.injEq, exists_eq_right', reduceCtorEq, and_false, exists_false, Sum.inr.injEq,
        or_false, false_or, or_self, implies_true, and_true, forall_and_index, forall_true_left,
        exists_eq_left, forall_eq_apply_imp_iff, forall_eq, forall_const]
      · simp only [Category.rcomp, Category.comp, ↓existsAndEq, true_and, Sum.exists,
        Sum.inl.injEq, exists_eq_right', reduceCtorEq, and_false, exists_false, Sum.inr.injEq,
        or_false, false_or, or_self, implies_true, and_true, forall_and_index, forall_true_left,
        exists_eq_left, forall_eq_apply_imp_iff, forall_eq, forall_const,
        IsEmpty.forall_iff, Sum.forall, false_and]
        intros r' m'
        constructor
        · intro ⟨h₁,h₂⟩
          rw[h₁,h₂]
          exact And.intro rfl rfl
        · intro ⟨h₁,h₂⟩
          rw[h₁,h₂]
          exact And.intro rfl rfl

/-  Conjoin events -/

def conj_NDEvent [Machine CTX M]  (ev₁ : NDEvent M α β) (ev₂ : NDEvent M α β)
  : NDEvent M α β :=
  {
    guard := fun m x => ev₁.guard m x ∨ ev₂.guard m x
    effect := fun m x _ (y, m') =>
      ((grd₁ : ev₁.guard m x) → ev₁.effect m x grd₁ (y, m'))
      ∧ ((grd₂ : ev₂.guard m x) → ev₂.effect m x grd₂ (y, m'))
  }

def impossible_NDEvent [Machine CTX M] : NDEvent M α β :=
  {
    guard _ _ := False
    effect := fun _ _ _ (_,_) => False
  }



instance [Machine CTX M] [Semigroup M]: ArrowPlus (NDEvent M) where
  zero := impossible_NDEvent
  conjoin := conj_NDEvent

instance [Machine CTX M] [Semigroup M] : LawfulArrowPlus (NDEvent M) where
    assoc :=
    by
      intros α β ev₁ ev₂ ev₃
      simp[ArrowPlus.conjoin]
      apply NDEvent.ext'
      simp[conj_NDEvent]
      intros m x
      constructor
      · constructor
        · intro h
          exact or_assoc.mp h
        · intro h
          exact or_assoc.mpr h
      · intros y m' grd₁ grd₂
        constructor
        · simp
          intros effectₗ effectᵣ
          constructor
          · intro grd₁'
            have ⟨h,_⟩ := effectₗ (Or.inl grd₁')
            exact h grd₁'
          · intro grd₂'
            constructor
            · cases grd₂'
              case right.mp.right.left.inl l =>
                exact (effectₗ (Or.inr l)).2
              case right.mp.right.left.inr r =>
                intro grd₂'
                exact (effectₗ (Or.inr grd₂')).2 grd₂'
            · assumption
        · simp
          intros effectₗ effectᵣ
          constructor
          · intro hgrd
            constructor
            · intro grd₁'
              exact (effectₗ grd₁')
            · intro grd₂'
              exact ((effectᵣ (Or.inl grd₂')).1 grd₂')
          · intro grd₃
            exact ((effectᵣ (Or.inr grd₃)).2 grd₃)
    comm_id :=
      by
        intros α β a
        simp[ArrowZero.zero]
        simp[ArrowPlus.conjoin]

        constructor
        · refine
          NDEvent.ext'
            (conj_NDEvent a { guard := fun x x => False, effect := fun m x x x => False })
            (conj_NDEvent { guard := fun x x => False, effect := fun m x x x =>False } a) ?_
          intros m x
          simp[conj_NDEvent]
        · simp[conj_NDEvent,impossible_NDEvent]
          constructor
          · refine
            NDEvent.ext' a
              { guard := fun m x => a.guard m x ∨ False,
                effect := fun m x x_1 x_2 => ∀ (grd₁ : a.guard m x), a.effect m x grd₁ x_2 }
              ?_
            simp
            intros m x y m' p
            exact Or.inl p
          · refine
            NDEvent.ext' a
              { guard := fun m x => False ∨ a.guard m x,
                effect := fun m x x_1 x_2 => ∀ (grd₂ : a.guard m x), a.effect m x grd₂ x_2 }
              ?_
            simp
            intros
            apply Or.inl
            assumption
