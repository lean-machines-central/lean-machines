

-- Contravariant functors
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

-- Profunctor and optics from
-- cf. https://github.com/hablapps/DontFearTheProfunctorOptics

class Profunctor (pf : Type u → Type v → Type w) where
  dimap {α β : Type u} {γ δ : Type v}:
          (β → α) → (γ → δ) → pf α γ → pf β δ
  lmap {α β : Type u} {γ : Type v}:
          (β → α) → pf α γ → pf β γ := fun f => dimap f id
  rmap {α β : Type v} {γ : Type u}:
          (α → β) → pf γ α → pf γ β := dimap id

open Profunctor

class LawfulProfunctor (pf : Type u → Type v → Type w) [Profunctor pf] : Prop where
  dimap_id (x : pf α β): dimap id id x = id x

  dimap_comp {α α' β : Type u} {γ γ' δ : Type v}
    (f : β → α') (f' : α' → α) (g : γ' → δ) (g' : γ → γ') (x : pf α γ):
    dimap (pf:=pf) (f' ∘ f) (g ∘ g') x
    = ((dimap f g) ∘ (dimap f' g')) x

section ProFun

instance: Profunctor (·→·) where
  dimap f h g := h ∘ g ∘ f

instance: LawfulProfunctor (·→·) where
  dimap_id f := by rfl
  dimap_comp f f' g g' x := by rfl

end ProFun
