
theorem Nat_sub_add_comm_cancel (a b c : Nat):
  b ≤ a → a - b + (c + b) = a + c :=
by
  intro H
  have H₁ : a - b + (c + b) = (a - b + b) + c := by simp_arith
  have H₂ : a - b + b = a := Nat.sub_add_cancel H
  simp [H₁, H₂]

theorem Nat_add_sub_comm_cancel (a b c : Nat):
  b ≤ c → a + b + (c - b) = a + c :=
by
  intro H
  have H₁ : a + b + (c - b) = a + (c - b + b) := by simp_arith
  have H₂ : c - b + b = c := by exact Nat.sub_add_cancel H
  simp [H₁, H₂]
