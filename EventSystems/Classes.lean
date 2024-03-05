

class Contravariant (f : Type u → Type v) : Type (max (u + 1) v) where
  contramap : {α β : Type u} → (α → β) → f β → f α
  contraConst : {α β : Type u} → β → f β → f α := fun b => contramap (fun _ => b)
