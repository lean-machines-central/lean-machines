

/- Contravariant functors -/

-- cf. https://blog.ocharles.org.uk/blog/guest-posts/2013-12-21-24-days-of-hackage-contravariant.html

class ContravariantFunctor (cf : Type u → Type v) where
  contramap {α β}:  (β → α) → cf α → cf β
  contraConst {α β}:  α → cf α → cf β := fun b => contramap (fun _ => b)

open ContravariantFunctor

class LawfullContravariantFunctor (cf : Type u → Type v) [ContravariantFunctor cf] : Prop where
  cmap_id (y : cf α) : contramap id y = y
  cmap_comp {α β γ} (f : β → γ) (g : γ → α) : contramap (g ∘ f) = (contramap f) ∘ (contramap (cf:=cf) g)

section ContraFun

universe u

@[simp]
abbrev CoFun (α β : Type u) := β → α

instance : ContravariantFunctor (CoFun γ) where
  contramap {α β : Type u} (f : β → α)  (g : CoFun γ α) := g ∘ f

instance : LawfullContravariantFunctor (CoFun γ) where
  cmap_id {α} (g : CoFun γ α) := by rfl
  cmap_comp {α β γ} (f : β → γ) (g : γ → α) := by rfl

end ContraFun

infixl:40 " >$< " => ContravariantFunctor.contramap

namespace ContravariantFunctor

@[simp]
def cmapConst [ContravariantFunctor cf]: β → cf β → cf α :=
  contramap ∘ (fun x _ => x)

@[simp]
def constCmap [ContravariantFunctor cf]: cf β → β → cf α :=
  flip cmapConst

def mapConst [Functor f] : α → f β → f α :=
  Functor.map ∘ (fun x _ => x)

def constMap [Functor f] : f β → α → f α :=
  flip mapConst

def phantom [Functor f] [ContravariantFunctor f] (x : f α) : f β :=
  constCmap (constMap x ()) ()

end ContravariantFunctor
