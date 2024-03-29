
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

theorem Eq_fun (e₁ : α → β) (e₂ : α → β):
  (fun x : α => e₁ x) = (fun y : α => e₂ y)
  → e₁ = e₂ :=
by
  intro Heq
  exact Heq
