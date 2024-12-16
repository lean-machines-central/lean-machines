import LeanMachines.Event.Basic
import LeanMachines.NonDet.Basic

/-!
# Ordinary Non-deterministic events

This module defines the user-level API for constructing
and manipulating **ordinary non-deterministic** events.
(cf. `Even/Ordinary` module for the deterministic case).

There are importance differences with deterministic events:

- the functional action of deterministic events is replaced by a
relational notion of effect

- a feasibility proof obligation is added to the safety requirement

-/

/-!
## Transitional events
-/

/-- The internal representation of proof obligations for ordinary
non-deterministic events. -/
structure _NDEventPO [Machine CTX M] (ev : _NDEvent M α β) (kind : EventKind) where
  safety (m : M) (x : α):
    Machine.invariant m
    → (grd : ev.guard m x)
    → ∀ y, ∀ m', ev.effect m x grd (y, m')
                 → Machine.invariant m'

  feasibility (m : M) (x : α):
    Machine.invariant m
    → (grd : ev.guard m x)
    → ∃ y, ∃ m', ev.effect m x grd (y, m')

/-- The type of non-deterministic events without convergence properties.
It is an event for machine type `M` with input type `α` and output type `β` -/
structure OrdinaryNDEvent (M) [Machine CTX M] (α) (β) extends _NDEvent M α β where
  po : _NDEventPO to_NDEvent  (EventKind.TransNonDet Convergence.Ordinary)

theorem OrdinaryNDEvent.ext [Machine CTX M] (ev₁ : OrdinaryNDEvent M α β) (ev₂ : OrdinaryNDEvent M α β):
  ev₁.to_NDEvent = ev₂.to_NDEvent
  → ev₁ = ev₂ :=
by
  cases ev₁ ; cases ev₂ ; simp


@[simp]
def OrdinaryEvent.toOrdinaryNDEvent [Machine CTX M] (ev : OrdinaryEvent M α β) : OrdinaryNDEvent M α β :=
  let event := ev.to_Event.to_NDEvent
{
  guard := event.guard
  effect := event.effect
  po := {
    safety := fun m x => by simp [event]
                            intro Hinv Hgrd
                            apply ev.po.safety m x Hinv Hgrd

    feasibility := fun m x => by simp [event]
  }
}

/-- The specification of a non-deterministic, ordinary event for machine `M`
with input type `α` and output type `β`. . -/
structure NDEventSpec (M) [Machine CTX M] (α) (β) where
  /-- The guard property of the event, in machine state `m` with input `x`. -/
  guard (m : M) (x : α) : Prop := True

  /-- The (non-deterministic) effect of the event, with
      previous machine state `m` and input `x`, with relation to  pair
      `(y, m')` with `y` an output value and `m'` the next machine state.

      **Remark: the guard property is supposed valid any time the effect
      must hold in the POs. However, this is not captured
      at the type level (a type-level guard-dependent variant is currently being
      investigated). -/
  effect (m : M) (x : α) (grd : guard m x) (_ : β × M) : Prop

  /-- The safety proof obligation. -/
  safety (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ y, ∀ m', effect m x grd (y, m')
                 → Machine.invariant m'

  /-- The feasibility proof obligation.
  This PO may be difficult to establish concretely in some models.
  In this case it is still considered an important
  axiom (which means a Lean4 axiom should be used to discharge the PO).
  -/
  feasibility (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∃ y, ∃ m', effect m x grd (y, m')

@[simp]
def NDEventSpec.to_NDEvent [Machine CTX M] (ev : NDEventSpec M α β) : _NDEvent M α β :=
  { guard := ev.guard
    effect := ev.effect
  }

/-- Construction of an ordinary non-deterministic event from a
`NDEventSpec` specification. -/
@[simp]
def newNDEvent {M} [Machine CTX M] (ev : NDEventSpec M α β) : OrdinaryNDEvent M α β :=
  {
    to_NDEvent := ev.to_NDEvent
    po := { safety := fun m x => by simp
                                    intros Hinv Hgrd
                                    apply ev.safety ; assumption
            feasibility := fun m x => by simp
                                         intros Hinv Hgrd
                                         apply ev.feasibility ; assumption
    }
  }

/-- Variant of `NDEventSpec` with implicit `Unit` output type -/
structure NDEventSpec' (M) [Machine CTX M] (α) where
  guard (m : M) (x : α) : Prop := True
  effect (m : M) (x : α) (grd : guard m x) (m' : M) : Prop

  safety (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ m', effect m x grd m'
            → Machine.invariant m'

  feasibility (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∃ m', effect m x grd m'

@[simp]
def NDEventSpec'.toNDEventSpec [Machine CTX M] (ev : NDEventSpec' M α) : NDEventSpec M α Unit :=
  { guard := ev.guard
    effect := fun m x grd ((), m') => ev.effect m x grd m'
    safety := fun m x => by simp ; apply ev.safety
    feasibility := fun m x => by simp ; apply ev.feasibility
  }

/-- Variant of `newNDEvent` with implicit `Unit` output type -/
@[simp]
def newNDEvent' {M} [Machine CTX M] (ev : NDEventSpec' M α) : OrdinaryNDEvent M α Unit :=
  newNDEvent ev.toNDEventSpec

/-- Variant of `NDEventSpec` with implicit `Unit` input and output types -/
structure NDEventSpec'' (M) [Machine CTX M] where
  guard (m : M) : Prop := True
  effect (m : M) (grd : guard m) (m' : M) : Prop

  safety (m : M):
    Machine.invariant m
    → (grd : guard m)
    → ∀ m', effect m grd m'
            → Machine.invariant m'

  feasibility (m : M):
    Machine.invariant m
    → (grd : guard m)
    → ∃ m', effect m grd m'

@[simp]
def NDEventSpec''.toNDEventSpec [Machine CTX M] (ev : NDEventSpec'' M) : NDEventSpec M Unit Unit :=
  { guard := fun m _ => ev.guard m
    effect := fun m () grd ((), m') => ev.effect m grd m'
    safety := fun m x => by
      simp
      intros Hinv Hgrd m' Heff
      exact ev.safety m Hinv Hgrd m' Heff
    feasibility := fun m x => by
      simp
      intros Hinv Hgrd
      exact ev.feasibility m Hinv Hgrd
  }

/-- Variant of `newNDEvent` with implicit `Unit` input and output types -/
@[simp]
def newNDEvent'' {M} [Machine CTX M] (ev : NDEventSpec'' M) : OrdinaryNDEvent M Unit Unit :=
  newNDEvent ev.toNDEventSpec

/-!
## Initialiazation events
-/

/-- The internal representation of proof obligations for initialization events. -/
structure _InitNDEventPO [Machine CTX M] (ev : _InitNDEvent M α β) (kind : EventKind) where
  safety (x : α):
    (grd : ev.guard x)
    → ∀ y, ∀ m', ev.init x grd (y, m')
                 → Machine.invariant m'

  feasibility (x : α):
    (grd : ev.guard x)
    → ∃ y, ∃ m', ev.init x grd (y, m')

/-- Type type of non-deterministic initialization events.
It is an event for machine type `M` with input type `α` and output type `β` -/
structure InitNDEvent (M) [Machine CTX M] (α) (β) extends _InitNDEvent M α β where
  po : _InitNDEventPO to_InitNDEvent  EventKind.InitNonDet

/-- The specification of a non-deterministic intialization event for machine `M`
with input type `α` and output type `β`.
The effect of the event is called an `init`.
-/
structure InitNDEventSpec (M) [Machine CTX M] (α) (β) where
  /-- The guard property of the event, an initialization with input `x`. -/
  guard (x : α) : Prop := True
  /-- The (non-deterministic) effect of the event, with
      previous machine state `m` and input `x`, with relation to  pair
      `(y, m')` with `y` an output value and `m'` the next machine state. -/
  init (x : α) (grd : guard x) (_ : β × M) : Prop
  /-- The safety proof obligation. -/
  safety (x : α):
    (grd : guard x)
    → ∀ y, ∀ m, init x grd (y, m)
                → Machine.invariant m
  /-- The feasibility proof obligation. -/
  feasibility (x : α):
    (grd : guard x)
    → ∃ y, ∃ m, init x grd (y, m)

@[simp]
def InitNDEventSpec.to_InitNDEvent [Machine CTX M]
  (ev : InitNDEventSpec M α β) : _InitNDEvent M α β :=
  {
    guard := ev.guard
    init := ev.init
  }

/-- Construction of a on-deterministic initialization event from a
`InitNDEventSpec` specification. -/
@[simp]
def newInitNDEvent {M} [Machine CTX M] (ev : InitNDEventSpec M α β) : InitNDEvent M α β :=
  {
    to_InitNDEvent := ev.to_InitNDEvent
    po := {
      safety := fun x => by simp ; intros ; apply ev.safety x <;> assumption
      feasibility := fun x => by
        intros Hgrd
        exact ev.feasibility x Hgrd
    }
  }

/-- Variant of `InitNDEventSpec` with implicit `Unit` output type -/
structure InitNDEventSpec' (M) [Machine CTX M] (α) where
  guard (x : α) : Prop := True
  init (x : α) (grd : guard x) (m : M) : Prop

  safety (x : α):
    (grd : guard x)
    → ∀ m, init x grd m
           → Machine.invariant m

  feasibility (x : α):
    (grd : guard x)
    → ∃ m, init x grd m

@[simp]
def InitNDEventSpec'.toInitNDEventSpec [Machine CTX M] (ev : InitNDEventSpec' M α) : InitNDEventSpec M α Unit :=
  {
    guard := ev.guard
    init := fun x grd ((), m) => ev.init x grd m
    safety := fun x => by
      simp
      intros Hgrd m Hini
      apply ev.safety x Hgrd ; assumption
    feasibility := fun x => by
      simp
      intros Hgrd
      apply ev.feasibility x Hgrd
  }

/-- Variant of `newInitNDEvent` with implicit `Unit` output type -/
@[simp]
def newInitNDEvent' [Machine CTX M] (ev : InitNDEventSpec' M α) : InitNDEvent M α Unit :=
  newInitNDEvent ev.toInitNDEventSpec


/-- Variant of `InitNDEventSpec` with implicit `Unit` input and output types -/
structure InitNDEventSpec'' (M) [Machine CTX M] where
  guard : Prop := True
  init (grd : guard) (m : M) : Prop

  safety:
    (grd : guard)
    → ∀ m, init grd m
           → Machine.invariant m

  feasibility:
    (grd : guard)
    → ∃ m, init grd m

@[simp]
def InitNDEventSpec''.toInitNDEventSpec [Machine CTX M] (ev : InitNDEventSpec'' M) : InitNDEventSpec M Unit Unit :=
  {
    guard := fun () => ev.guard
    init := fun () grd ((), m) => ev.init grd m
    safety := fun x => by
      simp
      intros Hgrd m Hini
      apply ev.safety Hgrd ; assumption
    feasibility := fun x => by
      simp
      intros Hgrd
      apply ev.feasibility Hgrd
  }

/-- Variant of `newInitNDEvent` with implicit `Unit` input and output types -/
@[simp]
def newInitNDEvent'' [Machine CTX M] (ev : InitNDEventSpec'' M) : InitNDEvent M Unit Unit :=
  newInitNDEvent ev.toInitNDEventSpec

/-!
## Algebraic properties of events

The following instantiate various algebraic structures, complementing
the structural properties of the representation types (`_NDEvent`) with
more "lawful" properties for the main event type (`OrdinaryNDEvent`).

This part is rather experimental and is thus not fully documented yet.

-/

instance [Machine CTX M] : Functor (OrdinaryNDEvent M γ) where
  map {α β} (f : α → β) event :=
  let ev' : _NDEvent M γ β := f <$> event.to_NDEvent
  {
    guard := ev'.guard
    effect := ev'.effect
    po := {
      safety := fun m z => by simp [ev', Functor.map]
                              intros Hinv Hgrd _ m' x Heff _
                              apply event.po.safety m z Hinv Hgrd x m' Heff
      feasibility := fun m z => by simp [ev', Functor.map]
                                   intros Hinv Hgrd
                                   have Hfeas := event.po.feasibility m z Hinv Hgrd
                                   obtain ⟨y, m', Hfeas⟩ := Hfeas
                                   exists (f y)
                                   exists m'
                                   exists y
    }
  }

-- XXX: proofs are a little bit painful due to the existentials ...
instance [Machine CTX M] : LawfulFunctor (OrdinaryNDEvent M γ) where
  map_const := rfl
  id_map ev := by simp [Functor.map]

  comp_map g h ev := by simp [Functor.map]
                        cases ev
                        case mk _ev _po =>
                          simp
                          have Hcm := LawfulFunctor.comp_map g h _ev
                          simp [Functor.map] at Hcm
                          assumption

/- XXX:
--  The output contravariant functor not provable, because we would
-- need a iso morphisme between α and β.
instance [Machine CTX M] : ContravariantFunctor (OrdinaryNDEvent M γ) where
  contramap {α β} (f : β → α) event :=
  let ev' : _NDEvent M γ β := ContravariantFunctor.contramap f event.to_NDEvent
  {
    guard := ev'.guard
    effect := ev'.effect
    po := {
      safety := fun m x => by simp [ev', ContravariantFunctor.contramap]
                              intros Hinv Hgrd y m' Heff
                              apply event.po.safety m x Hinv Hgrd (f y) m' Heff
      feasibility := fun m x => by simp [ev', ContravariantFunctor.contramap]
                                   intros Hinv Hgrd
                                   have Hfeas := event.po.feasibility m x Hinv Hgrd
                                   obtain ⟨y, m', Hfeas⟩ := Hfeas



    }
  }
-/


-- The input contravariant functor
abbrev CoOrdinaryNDEvent (M) [Machine CTX M] (α) (β) := OrdinaryNDEvent M β α


@[simp]
def CoOrdinaryNDEvent_from_OrdinaryNDEvent [Machine CTX M] (ev : OrdinaryNDEvent M α β) : CoOrdinaryNDEvent M β α :=
 ev

@[simp]
def OrdinaryNDEvent_from_CoOrdinaryNDEvent [Machine CTX M] (ev : CoOrdinaryNDEvent M β α) : OrdinaryNDEvent M α β :=
 ev

instance [Machine CTX M] : ContravariantFunctor (CoOrdinaryNDEvent M γ) where
  contramap {α β} (f : β → α) event :=
  let ev : _CoNDEvent M γ β := ContravariantFunctor.contramap f event.to_NDEvent
  {
     guard := ev.guard
     effect := ev.effect
     po := {
      safety := fun m x => by simp
                              revert ev
                              cases event
                              case mk _ev po =>
                                simp [ContravariantFunctor.contramap]
                                intros Hinv Hgrd y m' Heff
                                apply po.safety m (f x) Hinv Hgrd y m' Heff
      feasibility := fun m x => by simp
                                   intro Hinv
                                   revert ev
                                   cases event
                                   case mk _ev po =>
                                     simp [ContravariantFunctor.contramap]
                                     apply po.feasibility m (f x) Hinv

     }
  }

instance [Machine CTX M] : LawfullContravariantFunctor (CoOrdinaryNDEvent M γ) where
  cmap_id _ := rfl
  cmap_comp _ _ := rfl

instance [Machine CTX M] : Profunctor (OrdinaryNDEvent M) where
  dimap {α β} {γ δ} (f : β → α) (g : γ → δ) (ev : OrdinaryNDEvent M α γ) : OrdinaryNDEvent M β δ :=
  let ev' := OrdinaryNDEvent_from_CoOrdinaryNDEvent (ContravariantFunctor.contramap f (CoOrdinaryNDEvent_from_OrdinaryNDEvent ev))
  g <$> ev'


instance [Machine CTX M] : LawfulProfunctor (OrdinaryNDEvent M) where
  dimap_id := by simp [Profunctor.dimap, ContravariantFunctor.contramap]
                 exact fun {α β} => rfl
  dimap_comp f f' g g' := by funext event
                             have Hdc' := LawfulProfunctor.dimap_comp (pf:=_NDEvent M) f f' g g'
                             have Hdc : Profunctor.dimap (f' ∘ f) (g ∘ g') event.to_NDEvent = (Profunctor.dimap f g ∘ Profunctor.dimap f' g') event.to_NDEvent := by
                               exact congrFun Hdc' event.to_NDEvent
                             cases event
                             case _ ev po =>
                               cases po
                               case mk safe feas =>
                                 simp at *
                                 simp [Profunctor.dimap, ContravariantFunctor.contramap, Functor.map] at *
                                 simp [*]

instance [Machine CTX M] : StrongProfunctor (OrdinaryNDEvent M) where
  first' {α β γ} (event : OrdinaryNDEvent M α β): OrdinaryNDEvent M (α × γ) (β × γ) :=
    let ev : _NDEvent M (α × γ) (β × γ) := StrongProfunctor.first' event.to_NDEvent
    {
      guard := ev.guard
      effect := ev.effect
      po := {
        safety := fun m (x, z) => by simp [ev, StrongProfunctor.first']
                                     intros Hinv Hgrd
                                     have Hsafe := event.po.safety m x Hinv Hgrd
                                     intros y _ m' _ Heff
                                     exact Hsafe y m' Heff

        feasibility := fun m (x, z) => by simp [ev, StrongProfunctor.first']
                                          intro Hinv Hgrd
                                          have Hfeas := event.po.feasibility m x Hinv Hgrd
                                          obtain ⟨y, m', Hfeas⟩ := Hfeas
                                          exists y ; exists m'
      }
    }

instance [Machine CTX M] : LawfulStrongProfunctor (OrdinaryNDEvent M) where

instance [Machine CTX M]: Category (OrdinaryNDEvent M) where
  id {α }:=
  let ev : _NDEvent M α α := Category.id
  {
    guard := ev.guard
    effect := ev.effect
    po := {
      safety := fun m x => by simp [ev]
      feasibility := fun m x => by simp [ev]
    }
  }

  comp {α β γ} (ev₂ : OrdinaryNDEvent M β γ) (ev₁ : OrdinaryNDEvent M α β) : OrdinaryNDEvent M α γ :=
    let ev : _NDEvent M α γ := Category.comp ev₂.to_NDEvent ev₁.to_NDEvent
    { guard := ev.guard
      effect := ev.effect
      po := {
        safety := fun m x => by simp
                                intros Hinv
                                have Hsafe₁ := ev₁.po.safety m x Hinv
                                have Hsafe₂ := ev₂.po.safety
                                simp [ev] at *
                                intros Hgrd₁ Hev₂ z m'' y m' Heff₁ Heff₂
                                have Hsafe₁ := Hsafe₁ Hgrd₁ y m' Heff₁
                                apply Hsafe₂ m' y Hsafe₁ (Hev₂ y m' Heff₁) z m'' Heff₂
        feasibility := fun m x => by simp [ev]
                                     intros Hinv Hgrd
                                     have Hfeas₁ := ev₁.po.feasibility m x Hinv Hgrd
                                     obtain ⟨y, m', Heff₁⟩ := Hfeas₁
                                     have Hfeas₂ := ev₂.po.feasibility m' y
                                     have Hsafe₁ := ev₁.po.safety m x Hinv Hgrd y m' Heff₁
                                     intro Hgrd₂
                                     have Hgrd₂ := Hgrd₂ y m' Heff₁
                                     have Hfeas₂ := Hfeas₂ Hsafe₁ Hgrd₂
                                     obtain ⟨y', m'', Heff₂⟩ := Hfeas₂
                                     exists y' ; exists m'' ; exists y ; exists m'
      }
    }

instance [Machine CTX M]: LawfulCategory (OrdinaryNDEvent M) where
  id_right ev := by simp
                    have Hir := LawfulCategory.id_right ev.to_NDEvent
                    simp at Hir
                    cases ev
                    case mk _ po =>
                      simp [Hir]

  id_left ev := by simp

  id_assoc ev₁ ev₂ ev₃ := by have Hia := LawfulCategory.id_assoc ev₁.to_NDEvent ev₂.to_NDEvent ev₃.to_NDEvent
                             simp [*] at *
                             cases ev₁
                             cases ev₂
                             cases ev₃
                             simp [Hia]

-- XXX: This axiom is required to obtain feasibility
axiom OrdinaryNDEvent_split_feasibility_ax {CTX} {M} [Machine CTX M] [Semigroup M] {α β α' β'} (ev₁ : _NDEvent M α β)  (ev₂ : _NDEvent M α' β')
  (m : M) (x : α) (x' : α'):
  (∃ y, ∃ m', ev₁.effect m x (y, m'))
  → (∃ y', ∃ m', ev₂.effect m x' (y', m'))
  → (∃ y, ∃ y', ∃ m', (Arrow.split ev₁ ev₂).effect m (x, x') ((y, y'), m'))

class ParallelMachine (M) [Machine CTX M] extends Semigroup M where
  par_safe (m₁ m₂ : M):
    Machine.invariant m₁
    → Machine.invariant m₂
    → Machine.invariant (m₁ * m₂)


instance [Machine CTX M] [ParallelMachine M]: Arrow (OrdinaryNDEvent M) where

  arrow {α β} (f : α → β) :=
    let event : _NDEvent M α β := Arrow.arrow f
    {
      guard := event.guard
      effect := event.effect
      po := {
        safety := fun m x => by simp [event, Arrow.arrow]
        feasibility := fun m x => by simp [event, Arrow.arrow]
      }
    }

  split {α α' β β'} (ev₁ : OrdinaryNDEvent M α β)  (ev₂ : OrdinaryNDEvent M α' β') : OrdinaryNDEvent M (α × α') (β × β') :=
    let event : _NDEvent M  (α × α') (β × β') := Arrow.split ev₁.to_NDEvent ev₂.to_NDEvent
    {
      guard := event.guard
      effect := event.effect
      po := {
        safety := fun m (x,x') => by simp [event, Arrow.split]
                                     intros Hinv Hgrd₁ Hgrd₂
                                     intros y y' m' m'₁ Heff₁ m'₂ Heff₂ Hm'
                                     have Hsafe₁ := ev₁.po.safety m x Hinv Hgrd₁ y m'₁ Heff₁
                                     have Hsafe₂ := ev₂.po.safety m x' Hinv Hgrd₂ y' m'₂ Heff₂
                                     rw [Hm']
                                     apply ParallelMachine.par_safe m'₁ m'₂ <;> assumption

        -- this could be called "weak feasibility"
        feasibility := fun m (x, x') => by simp [Arrow.split, event]
                                           intros Hinv Hgrd₁ Hgrd₂
                                           have Hfeas₁ := ev₁.po.feasibility m x Hinv Hgrd₁
                                           have Hfeas₂ := ev₂.po.feasibility m x' Hinv Hgrd₂
                                           obtain ⟨y₁, m'₁, Hfeas₁⟩ := Hfeas₁
                                           obtain ⟨y₂, m'₂, Hfeas₂⟩ := Hfeas₂
                                           exists y₁ ; exists y₂
                                           exists (m'₁ * m'₂)
                                           exists m'₁
                                           constructor
                                           · assumption
                                           exists m'₂
      }
    }

  -- XXX : once again, an explicit `first` must be defined because `first-from-split` does
  --       not satisfy the `arrow_unit` law
  first {α β γ : Type} (ev : OrdinaryNDEvent M α β) : OrdinaryNDEvent M (α × γ) (β × γ) :=
  let event : _NDEvent M (α × γ) (β × γ) := Arrow.first ev.to_NDEvent
  {
    guard := event.guard
    effect := event.effect
    po := {
      safety := fun m (x,y) => by simp [event, Arrow.first]
                                  intros Hinv Hgrd
                                  intros u _ m' Heff _
                                  apply ev.po.safety m x Hinv Hgrd u m' Heff

      feasibility := fun m (x,y) => by simp [event, Arrow.first]
                                       intros Hinv Hgrd
                                       have Hfeas := ev.po.feasibility m x Hinv Hgrd
                                       obtain ⟨y',m', Heff⟩ := Hfeas
                                       exists y' ; exists m'

    }
  }



instance [Machine CTX M] [ParallelMachine M]: LawfulArrow (OrdinaryNDEvent M) where
  arrow_id := by simp [Arrow.arrow]

  arrow_ext {α β γ } f :=
      by simp [Arrow.arrow, Arrow.first, Arrow.split]
         funext m (x₁, x₂) ((y₁, y₂), m')
         simp
         constructor <;> (intros ; simp [*])

  arrow_fun f g := by simp [Arrow.arrow]
                      have Hfun := LawfulArrow.arrow_fun (arr := _NDEvent M) f g
                      simp [Arrow.arrow] at Hfun
                      simp [Hfun]

  arrow_xcg ev g := by simp [Arrow.arrow, Arrow.first, Arrow.split]
                       funext m (x₁,x₂) ((y₁, y₂), m')
                       simp
                       constructor
                       · intro Hex
                         obtain ⟨xx₁, gx₂, mm, Hex⟩ := Hex
                         obtain ⟨⟨H₁,⟨H₂,H₃⟩⟩, ⟨m'₁, ⟨Heff₁, ⟨m'₂, Hex₂⟩⟩⟩⟩ := Hex
                         exists y₁ ; exists x₂
                         simp [*] at *
                         assumption
                       -- next
                       intro Hex
                       obtain ⟨yy₁, xx₂, ⟨⟨m'₁, ⟨Heff₁, ⟨mm, Hmm⟩⟩⟩, H⟩⟩ := Hex
                       exists x₁ ; exists (g x₂) ; exists m
                       simp [*]

  arrow_unit ev := by simp [Arrow.arrow, Arrow.first, Arrow.split]
                      funext m (x₁,x₂) (y,m')
                      simp
                      constructor
                      · intro Heff
                        exists x₁ ; exists m
                      -- next
                      simp

  arrow_assoc {α β γ δ} ev :=
      by simp [Arrow.arrow, Arrow.first]
         have Hasc := @LawfulArrow.arrow_assoc (arr:=_NDEvent M) _ _ α β γ δ ev.to_NDEvent
         simp [Arrow.arrow, Arrow.first] at Hasc
         simp [Hasc]
