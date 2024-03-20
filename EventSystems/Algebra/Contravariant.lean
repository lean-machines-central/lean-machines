

/- Contravariant functors -/

-- cf. https://blog.ocharles.org.uk/blog/guest-posts/2013-12-21-24-days-of-hackage-contravariant.html

class Contravariant (cf : Type u → Type v) where
  contramap {α β : Type u}:  (β → α) → cf α → cf β
  contraConst {α β : Type u}:  α → cf α → cf β := fun b => contramap (fun _ => b)

open Contravariant

class LawfullContravariant (cf : Type u → Type v) [Contravariant cf] : Prop where
  cmap_id (y : cf α) : contramap id y = y
  cmap_comp {α β γ : Type u} (f : β → γ) (g : γ → α) : contramap (g ∘ f) = (contramap f) ∘ (contramap (cf:=cf) g)

section ContraFun

universe u

@[simp]
abbrev CoFun (α β : Type u) := β → α

instance : Contravariant (CoFun γ) where
  contramap {α β : Type u} (f : β → α)  (g : CoFun γ α) := g ∘ f

instance : LawfullContravariant (CoFun γ) where
  cmap_id {α : Type u} (g : CoFun γ α) := by rfl
  cmap_comp {α β γ : Type u} (f : β → γ) (g : γ → α) := by rfl

end ContraFun
