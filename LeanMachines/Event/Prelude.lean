
theorem And_assoc₁ (P Q R : Prop):
  (P ∧ Q) ∧ R → P ∧ (Q ∧ R) := fun H ↦ and_assoc.mp H

theorem And_assoc₂ (P Q R : Prop):
  P ∧ (Q ∧ R) → (P ∧ Q) ∧ R := fun H ↦ and_assoc.mpr H

theorem And_assoc (P Q R : Prop):
  (P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R) := ⟨And_assoc₁ P Q R, And_assoc₂ P Q R⟩

theorem And_eq_assoc (P Q R : Prop):
  ((P ∧ Q) ∧ R) = (P ∧ (Q ∧ R)) := propext (And_assoc _ _ _)

theorem Eq_fun (e₁ : α → β) (e₂ : α → β):
  (fun x : α => e₁ x) = (fun y : α => e₂ y)
  → e₁ = e₂ := fun Heq ↦ Heq

inductive Either (α β : Type) where
| left : α → Either α β
| right : β → Either α β
deriving Repr
