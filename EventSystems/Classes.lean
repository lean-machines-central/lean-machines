

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

#check @dimap

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

#check @second'

def StrongProfunctor.defaultSecond'{α β γ : Type u} (pf) [instPF: StrongProfunctor pf]:=
  dimap swap_fun swap_fun ∘ @first' pf instPF α β γ

class LawfulStrongProfunctor (pf : Type u → Type u → Type w) [StrongProfunctor pf] extends LawfulProfunctor pf where

theorem comp_assoc:
  f ∘ g ∘ h = (f ∘ g) ∘ h := rfl

theorem swap_fun_convol:
  @swap_fun α β ∘ swap_fun = id :=
by
  funext x
  simp [swap_fun]

-- Law₁: first' ≡ dimap swap swap . second'
theorem StrongProfunctor.law₁ {α β γ : Type u} (pf) [instPF: StrongProfunctor pf] [LawfulStrongProfunctor pf]:
  @first' pf instPF α β γ =
  Profunctor.dimap swap_fun swap_fun ∘ defaultSecond' pf :=
by
  simp [defaultSecond']
  rw [comp_assoc]
  have H : (@dimap pf toProfunctor (γ × α) (α × γ) (γ × β) (β × γ) swap_fun swap_fun)
           ∘ (@dimap pf toProfunctor (α × γ) (γ × α) (β × γ) (γ × β) swap_fun swap_fun)
           = dimap (swap_fun ∘ swap_fun) (swap_fun ∘ swap_fun) := by
    rw [←LawfulProfunctor.dimap_comp]
  rw [H]
  simp [swap_fun_convol]
  simp [LawfulProfunctor.dimap_id]
  rfl

section ProFun

instance: Profunctor (·→·) where
  dimap f h g := h ∘ g ∘ f

instance: LawfulProfunctor (·→·) where
  dimap_id := by intros ; rfl
  dimap_comp _ _ _ _ := by rfl

instance: StrongProfunctor (·→·) where
  first' f := fun (x, y) => (f x, y)

instance: LawfulStrongProfunctor (·→·) where

end ProFun

/- Category and Arrow -/
-- ==> Haskell folklore

class Category (cat : Type u → Type u → Type v) where
  id : cat α α
  comp : {α β γ : Type u} → cat β γ → cat α β → cat α γ

infixr:90 " (.) " => Category.comp

attribute [simp] Category.id Category.comp

class LawfulCategory (cat : Type u → Type u → Type v) [instC: Category cat] where
  id_right (f : cat α β): f (.) Category.id = f
  id_left (f : cat α β): Category.id (.) f = f
  id_assoc {α β γ δ} (f : cat γ δ) (g : cat β γ) (h : cat α β):
    f (.) (g (.) h) = (f (.) g) (.) h

infixr:10 " (<<<) " => Category.comp

@[simp]
def Category.rcomp [Category cat] (f : cat α β) (g : cat β γ) : cat α γ := g (.) f

infixr:10 " (>>>) " => Category.rcomp

section CatFun

instance: Category (·→·) where
  id := id
  comp := (·∘·)

instance: LawfulCategory (·→·) where
  id_right _ := rfl
  id_left _ := rfl
  id_assoc _ _ _ := rfl

end CatFun

class Arrow (arr : Type u → Type u → Type v) extends Category arr where
  arrow : (α → β) → arr α β
  split {α α' β β' : Type u}: arr α β → arr α' β' → arr (α × α') (β × β')

  first {α β γ : Type u} (x : arr α β) : arr (α × γ) (β × γ) :=
    let cid : arr γ γ := id
    split x cid

  second {α β γ : Type u} (x : arr α β): arr (γ × α) (γ × β) :=
    let cid : arr γ γ := id
    split cid x

  fanout {α β β' : Type u} (f : arr α β) (g : arr α β') : arr α (β × β') :=
    let l : arr α (α × α) := arrow (fun x => (x, x))
    let r : arr (α × α) (β × β') := split f g
    l (>>>) r

-- XXX: for non-obvious reasons we cannot use the first function
--      for generating the rest although it is simpler than split
--      hence the following "default implementation" can be used
--      as a "tweak"
@[simp]
def Arrow.split_from_first {arr : Type u → Type u → Type v} [Category arr]
  (arrsw: {α β : Type u} → arr (α × β) (β × α))
  (fst : {α β γ : Type u} → arr α β → arr (α × γ) (β × γ))
  {α α' β β' : Type u} (f : arr α β) (g : arr α' β') : arr (α × α') (β × β') :=
  let ff : arr (α × α') (β × α') := fst f
  let swff : arr (β × α') (α'× β) := arrsw
  let fg : arr (α' × β) (β' × β) := fst g
  let swfg : arr (β' × β) (β × β') := arrsw
  ff (>>>) swff (>>>) fg (>>>) swfg

open Arrow

@[simp]
def fun_split (f : α → β) (g : α' → β') : (α × α') → (β × β') :=
  fun (x,x') => (f x, g x')

@[simp]
def pair_first {α β} (p : α × β) : α := p.1

@[simp]
def fun_first (f : α → β) : (α × γ) → (β × γ) :=
  fun (x,z) => (f x, z)

@[simp]
def fun_assoc {α β γ}: ((α × β) × γ) → (α × (β × γ)) :=
  fun ((a, b), c) => (a, (b, c))

class LawfulArrow (arr : Type u → Type u → Type v) [Arrow arr] extends LawfulCategory arr where
  arrow_id :  -- (arrow id) = id
    let cid : arr α α := Category.id
    arrow id = cid

  arrow_ext (f : α → β): -- first (arrow f) = arrow (fun_split f id)
    let afs : arr (α × γ) (β × γ):= arrow (fun_split f id)
    first (arrow f) = afs

  arrow_fun (f : α → β) (g : β → γ): -- arrow (f >>> g) = (arrow f) >>> (arrow g)
    let agof : arr α γ := arrow (g ∘ f)
    let af : arr α β := arrow f
    let ag : arr β γ := arrow g
    let af_ag := af (>>>) ag
    agof = af_ag

  arrow_xcg (f : arr α β) (g : β → α): -- first f >>> arr (id ⋆⋆⋆ g) = arr (id ⋆⋆⋆ g) >>> first f
    let lg : arr (α × β) (α × α) := arrow (fun_split id g)
    let lf : arr (α × α) (β × α) := first f
    let l : arr (α × β) (β × α) := lg (>>>) lf
    let rf : arr (α × β) (β × β) := first f
    let rg : arr (β × β) (β × α) := arrow (fun_split id g)
    let r : arr (α × β) (β × α) := rf (>>>) rg
    l = r

  arrow_unit (f : arr α β) : -- first f >>> arr fst = arr fst >>> f
    let lafst : arr (β × β) β := arrow pair_first
    let lf : arr (α × β) (β × β) := first f
    let l : arr (α × β) β := lf (>>>) lafst
    let rafst : arr (α × β) α := arrow pair_first
    let r : arr (α × β) β := rafst (>>>) f
    l = r

  arrow_assoc {α β γ δ : Type u} (f : arr α β): -- first (first f) >>> arr assoc = arr assoc >>> first f
    let lf : arr (α × γ) (β × γ) := first f
    let lff : arr ((α × γ) × δ)  ((β × γ) × δ) := first lf
    let lassoc : arr ((β × γ) × δ) (β × (γ × δ)) := arrow fun_assoc
    let l := lff (>>>) lassoc
    let rassoc : arr ((α × γ) × δ) (α × (γ × δ)) := arrow fun_assoc
    let rf : arr (α × (γ × δ)) (β × (γ × δ)) := first f
    let r := rassoc (>>>) rf
    l = r

section ArrowFun

instance: Arrow (·→·) where
 arrow := id
 split := fun_split

instance : LawfulArrow (·→·) where
  arrow_id := rfl
  arrow_ext _ := rfl
  arrow_fun _ _ := rfl
  arrow_xcg _ _ := rfl
  arrow_unit _ := rfl
  arrow_assoc _ := rfl

end ArrowFun

abbrev Kleisli (m : Type u → Type v) α β := α → m β

instance [Monad m]: Category (Kleisli m) where
  id := pure
  comp {α β γ} (f : Kleisli m β γ) (g : Kleisli m α β)  : Kleisli m α γ :=
    fun x => g x >>= f

instance [Monad m]: Arrow (Kleisli m) where
  arrow {α β} (f : α → β) := fun x => pure (f x)
  split {α α' β β'} (f : Kleisli m α β)  (g : Kleisli m α' β') := --→ arr (α × α') (β × β')
    fun p : α × α' =>  f p.1 >>= fun y => g p.2 >>= fun y' => pure (y, y')

instance [Monad m] [LawfulMonad m]: LawfulCategory (Kleisli m) where
  id_right _ := by simp
  id_left _ := by  simp
  id_assoc _ _ _ := by simp

instance [Monad m] [LawfulMonad m]: LawfulArrow (Kleisli m) where
  arrow_id := rfl
  arrow_ext _ := by simp [arrow, first]
  arrow_fun _ _ := by simp [arrow]
  arrow_xcg _ _ := by simp [arrow, first]
  arrow_unit _ := by simp [arrow, first]
  arrow_assoc _ := by simp [arrow, first]

-- Note: an arrow is naturally a covariant functor
def map_from_arrow [Arrow arr] (f : α → β) (x : arr γ α) : arr γ β :=
  let af : arr α β := arrow f
  x (>>>) af

-- And also a contravariant functor
def contramap_from_arrow [Arrow arr] (f : β → α) (x : arr α γ) : arr β γ :=
  let af : arr β α := arrow f
  af (>>>) x

-- But it is not applicative in that pure is not realizable
-- because arrows only consider pairs of input/output types
-- but we have an approximation :
def quasi_pure_from_arrow [Arrow arr] (x : α) : arr Unit α :=
  arrow (fun () => x)

/-
-- Apply would inject a function type within an arrow ... without a
-- way to apply it ... a deadend ...
def apply_from_arrow [Arrow arr] (af : arr γ (α → β)) (ax : arr γ α) : arr γ β :=
  by sorry
-/
