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

instance fcat: Category (·→·) where
  id := id
  comp := (·∘·)


instance: LawfulCategory (·→·) where
  id_right _ := rfl
  id_left _ := rfl
  id_assoc _ _ _ := rfl

end CatFun

class Arrow (arr : Type u → Type u → Type v) extends Category arr where
  arrow : (α → β) → arr α β
  split {α γ β δ : Type u}: arr α β → arr γ δ → arr (α × γ) (β × δ)

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
  id_left _ := by simp
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

def untag (s : Sum α α) : α :=
  match s with
  | .inl x => x
  | .inr x => x

/- Variants of the Arrow Typeclass -/

class ArrowChoice (arr : Type u → Type u → Type v) extends Arrow arr where
  splitIn : arr α β → arr γ δ → arr (Sum α γ) (Sum β δ)
  left : arr α β → arr (Sum α γ) (Sum β γ) := fun x => splitIn x Category.id
  right : arr α β → arr (Sum γ α) (Sum γ β) := let ia : arr γ γ := Category.id
                                               splitIn ia
  fanIn (f : arr α β) (g : arr γ β) : arr (Sum α γ) β :=
    (splitIn f g) (>>>) (arrow untag)

open ArrowChoice

instance fc : ArrowChoice (·→·) where
  splitIn f g := fun x => match x with
                          | .inl x => Sum.inl (f x)
                          | .inr y => Sum.inr (g y)

def assocsum : (Sum (Sum α β) γ) → (Sum α (Sum β γ)) :=
  λ s =>
  match s with
    | .inl (.inl x)=> .inl x
    | .inl (.inr y) => .inr (.inl y)
    | .inr z => .inr (.inr z)

class LawfulArrowChoice (arr : Type u → Type u → Type v) [ArrowChoice arr] extends LawfulArrow arr where
  left_arr (f : α → β) : -- left (arr f) = arr (left f)
    let lh : arr (Sum α γ) (Sum β γ) := left (arrow f)
    let rh : arr (Sum α γ) (Sum β γ) := arrow (fc.left f)
    lh = rh
  left_f_g (f : arr α β) (g : arr β γ) :
    let lh : arr (Sum α ω) (Sum γ ω) := left (f (>>>) g)
    let rh : arr (Sum α ω) (Sum γ ω) := (left f) (>>>) (left  g)
    lh = rh
  arr_inl (f :arr α β) :
    let lh : arr α (Sum β γ ) := f (>>>) (arrow (Sum.inl))
    let rh : arr α (Sum β γ ) := (arrow (Sum.inl)) (>>>) left f
    lh = rh
  split (f : arr α β) (g : α' →  β'):
    let lh := (left  f) (>>>) arrow (fc.splitIn id g)
    let rh : arr (Sum α α') (Sum β β' ):=  arrow (fc.splitIn id g) (>>>) (left f)
    lh = rh
  assoc (f : arr α β) :
    let arrassocsum : arr (Sum (Sum β δ) γ) (Sum β (Sum δ γ)):= arrow assocsum
    let lh := left (left f) (>>>) arrassocsum
    let rh := arrow assocsum (>>>) left f
    lh = rh

class ArrowZero (arr : Type u → Type u → Type v) extends Arrow arr where
  zero : arr α β

class ArrowPlus (arr : Type u → Type u → Type v) extends ArrowZero arr where
  conjoin : arr α β → arr α β → arr α β

class LawfulArrowPlus (arr : Type u → Type u → Type v) [ArrowPlus arr] extends LawfulArrow arr where
  assoc :
    let lh : arr α β := ArrowPlus.conjoin (ArrowPlus.conjoin a b) c
    let rh : arr α β := ArrowPlus.conjoin a (ArrowPlus.conjoin b c)
    lh = rh
  comm_id :
    let lh : arr α β := ArrowPlus.conjoin a ArrowZero.zero
    let rh : arr α β := ArrowPlus.conjoin ArrowZero.zero a
    lh = rh ∧ a = lh ∧ a = rh

class ArrowLoop (arr : Type u → Type u → Type u) extends Arrow arr where
  loop : arr (α  × γ) (β × γ) → arr α β

-- instance : ArrowLoop (· → ·) where
--   loop f b :=
--     let (c,d) := f (b,d)
--     c
