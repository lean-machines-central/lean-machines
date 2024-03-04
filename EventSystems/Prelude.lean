
theorem And_assoc₁ (P Q R : Prop):
  (P ∧ Q) ∧ R → P ∧ (Q ∧ R) :=
by
  intro H
  simp [H]

theorem And_assoc₂ (P Q R : Prop):
  P ∧ (Q ∧ R) → (P ∧ Q) ∧ R :=
by
  intro H
  simp [H]

theorem And_assoc (P Q R : Prop):
  (P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R) := ⟨And_assoc₁ P Q R, And_assoc₂ P Q R⟩

theorem And_eq_assoc (P Q R : Prop):
  ((P ∧ Q) ∧ R) = (P ∧ (Q ∧ R)) :=
by
  apply propext
  apply And_assoc
