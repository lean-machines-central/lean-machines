import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod

structure Course where
  name : String
deriving Repr, BEq, DecidableEq

structure Member where
  name : String
deriving Repr, BEq, DecidableEq


theorem Nat_sub_zero (a b : Nat):
  0 < a → a - b = a → b = 0 :=
by
  intro Hinf Hsub
  cases b
  case zero => simp
  case succ b =>
    have Hcontra: a - Nat.succ b < a := by
      apply Nat.sub_lt
      · assumption
      · simp_arith
    simp_arith [*] at *

theorem Nat_le_sub_add (a b c : Nat):
  b ≤ c
  → a ≤ a - b + c :=
by
  intro Hbc
  rw [← @Nat.sub_le_iff_le_add]
  exact Nat.sub_le_sub_left Hbc a

theorem Nat_lt_sub_add (a b c : Nat):
  b < c
  → a < a - b + c :=
by
  intros Hbc
  rw [@Nat.lt_iff_le_and_ne]
  constructor
  · apply Nat_le_sub_add ; apply Nat.le_of_lt Hbc
  · intro Hfalse
    by_cases a ≤ b
    case pos Hab =>
      have H₁: a - b = 0 := by exact Nat.sub_eq_zero_of_le Hab
      simp [H₁] at Hfalse
      rw [Hfalse] at Hab
      apply Nat.not_le_of_lt Hbc
      assumption
    case neg Hab =>
      have H₁ : a + b = a - b + c + b := by exact Nat.add_right_cancel_iff.mpr Hfalse
      have H₂ : a - b + c + b = a - b + b + c := by simp_arith
      rw [H₂] at H₁ ; clear H₂
      have H₃ : a - b + b = a  := by
        apply Nat.sub_add_cancel
        exact Nat.le_of_not_ge Hab
      rw [H₃] at H₁ ; clear H₃
      have H₄: b = c := by
        apply Nat.add_left_cancel (n:=a)
        assumption
      rw [H₄] at Hbc
      have H₅: ¬ (c < c) := by exact Nat.not_lt.mpr Nat.le.refl
      contradiction

theorem Finset_le_sdiff_sub [DecidableEq α] (s₁ s₂ : Finset α):
  (s₁ \ s₂).card ≤ s₁.card :=
by
  apply Finset.card_le_card
  apply Finset.sdiff_subset

theorem Finset_nonempty_ex (s : Finset α):
  s ≠ ∅ → ∃ x, x ∈ s :=
by
  intro Hs₁
  have Hs₂ : s.Nonempty := by exact Finset.nonempty_of_ne_empty Hs₁
  cases s.decidableNonempty
  case isFalse Hs' =>
    contradiction
  case isTrue Hs' =>
    assumption

theorem Finset_mem_product_left {a : α} {b : β} {s : Finset α} {t : Finset β}:
   (a, b) ∈ s ×ˢ t → a ∈ s :=
by
  intro Hab
  have H₁ := (Finset.mem_product (p:=(a,b)) (s:=s) (t:=t)).1 Hab
  simp at H₁
  simp [H₁]

theorem Finset_mem_product_right {a : α} {b : β} {s : Finset α} {t : Finset β}:
   (a, b) ∈ s ×ˢ t → b ∈ t :=
by
  intro Hab
  have H₁ := (Finset.mem_product (p:=(a,b)) (s:=s) (t:=t)).1 Hab
  simp at H₁
  simp [H₁]

theorem Finset_sdiff_insert_assoc [DecidableEq α] (s t : Finset α):
  x ∉ t
  → insert x (s \ t) = insert x s \ t :=
by
  intro Hx
  exact (Finset.insert_sdiff_of_not_mem s Hx).symm

theorem Finset_card_union_le [DecidableEq α] (s t : Finset α):
  s.card ≤ (s ∪ t).card :=
by
  rw [@Finset.card_union]
  have H₁: (s ∩ t).card ≤ t.card := by
    refine Finset.card_le_card ?_
    apply Finset.inter_subset_right
  apply Nat.le_sub_of_add_le'
  simp_arith [H₁]

theorem Finset_insert_mem [DecidableEq α] (x : α) (s : Finset α):
  x ∈ s → insert x s = s :=
by
  intro Hx
  exact Finset.insert_eq_self.mpr Hx

theorem Finset_insert_notmem [DecidableEq α] (x : α) (s : Finset α):
  x ∉ s → s ⊂ insert x s :=
by
  intro Hx
  exact Finset.ssubset_insert Hx

theorem Finset_ssubset_union [DecidableEq α] (x : α) (s t : Finset α):
  s ⊆ t → x ∉ s → s ⊂ t ∪ {x} :=
by
  intro Hsub Hx
  have H₁:= (Finset.ssubset_iff (s:=s) (t:=t ∪ {x})).mpr
  apply H₁
  exists x
  simp [Hx]
  intros y Hy
  simp [Hx] at Hy
  cases Hy
  case inl Hy =>
    simp [Hy]
  case inr Hy =>
    simp [Hy]
    left
    apply Hsub ; assumption

/-
theorem Finset_ex [DecidableEq α] (s t : Finset α):
  s ⊂ t → ∃ x ∈ t, x ∉ s :=
by
  intro Hsub
  exact Set.exists_of_ssubset Hsub
-/

theorem Finset_ssubset_insert_right [DecidableEq α] (s t : Finset α) (x : α):
  s ⊂ t → s ⊂ insert x t :=
by
  intro Hst
  have Hst' : s ⊆ t := by exact subset_of_ssubset Hst
  by_cases x ∈ s
  case pos Hx =>
    have Hx': x ∈ t := by exact Hst' Hx
    simp [Hx']
    assumption
  case neg Hx =>
    rw [@Finset.ssubset_iff]
    exists x
    simp [Hx]
    assumption

theorem Finset_ssubset_insert [DecidableEq α] (s t : Finset α) (x : α):
  s ⊂ t → x ∉ t → insert x s ⊂ insert x t :=
by
  intro Hst Hxt
  have Hst' : s ⊆ t := by exact subset_of_ssubset Hst
  by_cases x ∈ s
  case pos Hxs =>
    rw [Finset_insert_mem x s Hxs]
    exact Finset_ssubset_insert_right s t x Hst
  case neg _ =>
    have Hex: ∃ y ∈ t, y ∉ s := by exact Set.exists_of_ssubset Hst
    cases Hex
    case intro y Hy =>
      have Hyt: y ∈ insert x t := by simp [Hy]
      have Hys: y ∉ insert x s := by
        simp [Hy]
        intro Hfalse
        rw [←Hfalse] at Hxt
        have Hfalse': y ∈ t := by simp [Hy]
        contradiction
      apply HasSubset.Subset.ssubset_of_not_subset
      · exact Finset.insert_subset_insert x Hst'
      · exact fun a => Hys (a Hyt)

theorem Finset_ssubset_union_left [DecidableEq α] (s t₁ t₂ : Finset α):
  t₁ ⊂ t₂ → Disjoint s t₂
  → s ∪ t₁ ⊂ s ∪ t₂ :=
by
  intro H₁ H₂
  induction s using Finset.induction_on
  case empty => simp ; assumption
  case insert x s Hx Hind =>
    simp
    simp at H₂
    simp [H₂] at Hind
    refine Finset_ssubset_insert (s ∪ t₁) (s ∪ t₂) x Hind ?_
    simp [Hx, H₂]

theorem Finset_ssubset_of_subset [DecidableEq α] (s t : Finset α):
  s ⊆ t → (∃ x ∈ t, x ∉ s) →  s ⊂ t :=
by
  intros Hsub Hex
  exact (Finset.ssubset_iff_of_subset Hsub).mpr Hex

theorem Finset_subset_product_of_subsets (s : Finset α) (t : Finset β):
  (∀ cp ∈ cps, cp.1 ∈ s)
  → (∀ cp ∈ cps, cp.2 ∈ t)
  → cps ⊆ s ×ˢ t :=
by
  intros H₁ h₂
  intros cp Hcp
  exact Finset.mem_product.mpr { left := H₁ cp Hcp, right := h₂ cp Hcp }
