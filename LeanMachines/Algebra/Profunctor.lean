
import LeanMachines.Algebra.Arrow

/- Profunctor and optics -/

-- cf. https://github.com/hablapps/DontFearTheProfunctorOptics

class Profunctor (pf : Type u → Type v → Type w) where
  dimap {α β : Type u} {γ δ : Type v}:
          (β → α) → (γ → δ) → pf α γ → pf β δ
  lmap {α β : Type u} {γ : Type v}:
          (β → α) → pf α γ → pf β γ := fun f => dimap f id
  rmap {α β : Type v} {γ : Type u}:
          (α → β) → pf γ α → pf γ β := dimap id

open Profunctor

class LawfulProfunctor (pf : Type u → Type v → Type w) [instPF: Profunctor pf] : Prop where
  dimap_id {α : Type u} {β : Type v}: @dimap pf instPF α α β β id id = id

  dimap_comp {α α' β : Type u} {γ γ' δ : Type v}
    (f : β → α') (f' : α' → α) (g : γ' → δ) (g' : γ → γ'):
    dimap (pf:=pf) (f' ∘ f) (g ∘ g')
    = ((dimap f g) ∘ (dimap f' g'))

def swap_fun : α × β → β × α := fun (x, y) => (y, x)

-- Note : there is a further constraint on universe levels
class StrongProfunctor (pf : Type u → Type u → Type w) extends Profunctor pf where
  first' {α β γ : Type u}: pf α β → pf (α × γ) (β × γ)
  second' {α β γ : Type u}: pf α β → pf (γ × α) (γ × β) :=
    dimap swap_fun swap_fun ∘ first'

open StrongProfunctor

def StrongProfunctor.defaultSecond'{α β γ : Type u} (pf) [instPF: StrongProfunctor pf]:=
  dimap swap_fun swap_fun ∘ @first' pf instPF α β γ

def α_ : ((β × γ ) × δ) → (β × (γ × δ)) :=
  λ ((b,c),d) => (b,(c,d))

def α_inv :  (β × (γ × δ)) → ((β × γ ) × δ) :=
  λ (b,(c,d)) => ((b,c),d)

class LawfulStrongProfunctor (pf : Type u → Type u → Type w) [StrongProfunctor pf] extends LawfulProfunctor pf where
  -- well ... there *are* laws
  -- cf. https://arxiv.org/pdf/1406.4823.pdf
  dimap_pi_id (a : pf α β) :
    let lh : pf (α × γ) β := dimap id Prod.fst (first' a)
    let rh : pf (α × γ) β := dimap Prod.fst id a
    lh = rh
  first_first (a : pf α β):
    let lh : pf ((α × γ)× γ') ((β × γ)× γ') := first' (first' a)
    let rh : pf ((α × γ)× γ') ((β × γ)× γ') := dimap α_ α_inv (first' a)
    lh = rh
  dinaturality (a : pf α β) (f : γ  → δ):
    let lh : pf (α × γ) (β × δ) := dimap (λ (x,y) => (id x, f y)) id (first' a)
    let rh : pf (α × γ) (β × δ) := dimap id (λ (x,y) => (id x, f y)) (first' a)
    lh = rh




theorem comp_assoc:
  f ∘ g ∘ h = (f ∘ g) ∘ h := rfl

theorem swap_fun_convol:
  @swap_fun α β ∘ swap_fun = id := rfl

-- first' ≡ dimap swap swap . second'
theorem StrongProfunctor.first_dimap {α β γ : Type u} (pf) [instPF: StrongProfunctor pf] [LawfulStrongProfunctor pf]:
  @first' pf instPF α β γ =
  Profunctor.dimap swap_fun swap_fun ∘ defaultSecond' pf :=
by
  rw [defaultSecond', comp_assoc]
  have H : (@dimap pf toProfunctor (γ × α) (α × γ) (γ × β) (β × γ) swap_fun swap_fun)
           ∘ (@dimap pf toProfunctor (α × γ) (γ × α) (β × γ) (γ × β) swap_fun swap_fun)
           = dimap (swap_fun ∘ swap_fun) (swap_fun ∘ swap_fun) := by
    rw [←LawfulProfunctor.dimap_comp]
  rw [H]
  simp only [swap_fun_convol, LawfulProfunctor.dimap_id]
  rfl

section ProFun

instance: Profunctor (·→·) where
  dimap f h g := h ∘ g ∘ f

instance: LawfulProfunctor (·→·) where
  dimap_id := rfl
  dimap_comp _ _ _ _ := rfl

instance: StrongProfunctor (·→·) where
  first' f := fun (x, y) => (f x, y)

instance: LawfulStrongProfunctor (·→·) where
  dimap_pi_id a :=
  by
    -- simp[dimap,first']
    rfl
  first_first a :=
  by
    -- simp[dimap,first',α_,α_inv]
    rfl
  dinaturality a f :=
  by
    -- simp[dimap,first']
    rfl

end ProFun


-- Reconstruct a profunctor from an arrow
instance [Arrow arr]: Profunctor arr where
  dimap {α β γ δ}
        (f: β → α) (g: γ → δ) (x : arr α γ) : arr β δ :=
    (Arrow.arrow f) (>>>) x (>>>) (Arrow.arrow g)
