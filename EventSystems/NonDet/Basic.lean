
import EventSystems.Event.Prelude
import EventSystems.Event.Basic
import EventSystems.Event.Ordinary

structure _NDEvent (M) [Machine CTX M] (α) (β : Type)
  extends _EventRoot M α where

  effect: M → α → (β × M) → Prop

theorem _NDEvent.ext [Machine CTX M] (ev₁ : _NDEvent M α β) (ev₂ : _NDEvent M α β):
  ev₁.to_EventRoot = ev₂.to_EventRoot
  → ev₁.effect = ev₂.effect
  → ev₁ = ev₂ :=
by
  intros H₁ H₂
  cases ev₁
  case mk _evr₁ _eff₁ =>
    cases ev₂
    case mk _evr₃ _eff₂ =>
      simp [*] at *
      simp [H₁, H₂]

@[simp]
def _NDEvent_fromEvent [Machine CTX M] (ev : _Event M α β) : _NDEvent M α β :=
{
  guard := ev.guard
  effect := fun m x (x'', m'') => let (x', m') := ev.action m x
                                  m'' = m' ∧ x'' = x'
}

-- The functor instance is existential, not suprising given the relational context
instance [Machine CTX M] : Functor (_NDEvent M γ) where
  map f ev :=
  {
    guard := ev.guard
    effect := fun m x (y, m') => ∃ z, ∃ m'', ev.effect m x (z, m'')
                                             ∧ y = f z ∧ m' = m''
  }

instance [Machine CTX M] : LawfulFunctor (_NDEvent M γ) where
  map_const := rfl
  id_map ev := by simp [Functor.map]
                  cases ev
                  case mk evr Peff =>
                    simp
                    funext m x (y,m')
                    apply propext
                    constructor
                    · intro Hz
                      cases Hz
                      case _ z H =>
                        simp at H
                        simp [H]
                    intro Heff
                    simp
                    exists y

  comp_map g h ev := by simp [Functor.map]
                        funext m x (y,m')
                        apply propext
                        constructor
                        · intro Hz
                          cases Hz
                          case _ z H =>
                            simp at H
                            simp
                            exists (g z)
                            constructor
                            · exists z
                              simp [H]
                            simp [H]
                        simp
                        intros z t Heff Heq₁ Heq₂
                        exists t
                        simp [Heff, Heq₁, Heq₂]


-- There are two possible, distinct ContravariantFunctor functors
-- for non-deterministic events.

-- The first operates on the output, hence it cannot be use
-- in a profunctor context
instance [Machine CTX M] : ContravariantFunctor (_NDEvent M γ) where
  contramap f ev :=
  {
    guard := ev.guard
    effect := fun m x (y, m') => ev.effect m x ((f y), m')
  }

instance [Machine CTX M] : LawfullContravariantFunctor (_NDEvent M β) where
  cmap_id _ := rfl
  cmap_comp _ _ := rfl

-- The second operates on the input
abbrev _CoNDEvent (M) [Machine CTX M] (α) (β) := _NDEvent M β α

@[simp]
def CoNDEvent_from_NDEvent [Machine CTX M] (ev : _NDEvent M α β) : _CoNDEvent M β α :=
 ev

@[simp]
def NDEvent_from_CoNDEvent [Machine CTX M] (ev : _CoNDEvent M β α) : _NDEvent M α β :=
 ev


instance [Machine CTX M] : ContravariantFunctor (_CoNDEvent M γ) where
  contramap f ev :=
  {
     guard := fun m x => ev.guard m (f x)
     effect := fun m x (y, m')  => ev.effect m (f x) (y, m')
  }

instance [Machine CTX M] : LawfullContravariantFunctor (_CoNDEvent M γ) where
  cmap_id _ := rfl
  cmap_comp _ _ := rfl

-- There is a unique possible profunctor instance
instance [Machine CTX M] : Profunctor (_NDEvent M) where
  dimap {α β} {γ δ} (f : β → α) (g : γ → δ) (ev : _NDEvent M α γ) : _NDEvent M β δ :=
  let ev' := NDEvent_from_CoNDEvent (ContravariantFunctor.contramap f (CoNDEvent_from_NDEvent ev))
  g <$> ev'

instance [Machine CTX M] : LawfulProfunctor (_NDEvent M) where
  dimap_id := by simp [Profunctor.dimap, ContravariantFunctor.contramap]
                 exact fun {α β} => rfl
  dimap_comp f f' g g' := by simp [Profunctor.dimap, ContravariantFunctor.contramap, Functor.map]
                             funext ev
                             simp
                             funext m x (y,m')
                             simp
                             constructor
                             · intro Heff
                               cases Heff
                               case _ u Heff =>
                                 exists (g' u)
                                 simp [Heff]
                                 exists u
                                 simp [Heff]
                             intro Heff
                             cases Heff
                             case _ t Heff =>
                               simp at Heff
                               cases Heff
                               case _ Heff Hy =>
                                 cases Heff
                                 case _ u Heff =>
                                   exists u
                                   simp [Heff, Hy]

instance [Machine CTX M] : StrongProfunctor (_NDEvent M) where
  first' {α β γ} (ev : _NDEvent M α β): _NDEvent M (α × γ) (β × γ) :=
    {
      guard := fun m (x, _) => ev.guard m x
      effect := fun m (x,u) ((y, v), m') => v = u ∧ ev.effect m x (y, m')
    }

instance [Machine CTX M] : LawfulStrongProfunctor (_NDEvent M) where


instance [Machine CTX M]: Category (_NDEvent M) where
  id := {
    effect := fun m x (y, m') => y = x ∧ m' = m
  }

  comp {α β γ} (ev₂ : _NDEvent M β γ) (ev₁ : _NDEvent M α β) : _NDEvent M α γ :=
    { guard := fun m x => ev₁.guard m x ∧ (∀ y, ∀ m', ev₁.effect m x (y, m')
                                           → ev₂.guard m' y)
      effect := fun m x (z, m'') => ∃ y, ∃ m', ev₁.effect m x (y, m') ∧ ev₂.effect m' y (z, m'')
    }

instance [Machine CTX M]: LawfulCategory (_NDEvent M) where
  id_right ev := by cases ev
                    case mk evr eff =>
                      simp
                      funext m x (z, m'')
                      simp
                      constructor
                      · intros Heff
                        cases Heff
                        case _ y Heff =>
                          cases Heff
                          case _ m' Heff =>
                            cases Heff
                            case _ Heq Heff =>
                              simp [Heq] at Heff
                              assumption
                      intro Heff
                      exists x
                      exists m

  id_left ev := by cases ev
                   case mk evr eff =>
                     simp
                     funext m x (z, m'')
                     simp
                     constructor
                     · intro Heff
                       cases Heff
                       case _ y Heff =>
                         simp [Heff]
                     intro Heff
                     exists z

  id_assoc ev₁ ev₂ ev₃ := by
    cases ev₁
    case mk evr₁ eff₁ =>
      cases ev₂
      case mk evr₂ eff₂ =>
        cases ev₃
        case mk evr₃ eff₃ =>
          simp
          constructor
          case left =>
            funext m x
            case h.h =>
              simp
              constructor
              case mpr =>
                intros H₁
                cases H₁
                case intro Hgrd₃ H₁ =>
                  constructor
                  case left =>
                    simp [Hgrd₃]
                    intros y m' Heff₃
                    apply (H₁ y m' Heff₃).left
                  case right =>
                    intros z m'' y m' Heff₃ Heff₂
                    have H₁' := H₁ y m' Heff₃  ; clear H₁
                    cases H₁'
                    case intro Hgrd₂ Hgrd₁ =>
                      apply Hgrd₁ z m'' <;> assumption
              case mp =>
                  simp
                  intros Hgrd₃ Hgrd₂ Hgrd₁
                  constructor
                  case left =>
                    assumption
                  case right =>
                    intros y m' Heff₃
                    constructor
                    case left =>
                      apply Hgrd₂ <;> assumption
                    case right =>
                      intros z m'' Heff₂
                      apply Hgrd₁ z m'' <;> assumption
          case right =>
            funext m x (t, m₃)
            case h.h.h =>
              simp
              constructor
              case mp =>
                intro Hex
                cases Hex
                case intro z Hex =>
                  cases Hex
                  case intro m'' Hex =>
                  cases Hex
                  case intro Hex Heff₁ =>
                    cases Hex
                    case intro y Hex =>
                      cases Hex
                      case intro m' Heff =>
                        exists y
                        exists m'
                        simp [Heff]
                        exists z
                        exists m''
                        simp [Heff₁, Heff]
              case mpr =>
                intro Hex
                cases Hex
                case intro y Hex =>
                  cases Hex
                  case intro m' Hex =>
                    cases Hex
                    case intro Heff₃ Hex =>
                      cases Hex
                      case intro z Hex =>
                        cases Hex
                        case intro m'' Heff =>
                          exists z
                          exists m''
                          constructor
                          case left =>
                            exists y
                            exists m'
                            simp [Heff₃, Heff]
                          case right =>
                            simp [Heff]




@[simp]
def arrow_NDEvent (M) [Machine CTX M] (f : α → β) : _NDEvent M α β :=
  {
    effect := fun m x (y, m') => y = f x ∧ m' = m
  }

-- Split is simply parallel composition
@[simp]
def split_NDEvent [Machine CTX M] (ev₁ : _NDEvent M α β) (ev₂ : _NDEvent M γ δ) : _NDEvent M (α × γ) (β × δ) :=
  {
    guard := fun m (x, y) => ev₁.guard m x ∧ ev₂.guard m y
    effect := fun m (x, y) ((x', y'), m') => ev₁.effect m x (x', m') ∧ ev₂.effect m y (y', m')
  }

-- Remark: without an explicit first the law `arrow_unit` is not provable
@[simp]
def first_NDEvent [Machine CTX M] (ev : _NDEvent M α β) : _NDEvent M (α × γ) (β × γ) :=
  {
    guard := fun m (x, _) => ev.guard m x
    effect := fun m (x, y) ((x', y'), m') => ev.effect m x (x', m') ∧ y'= y
  }

-- An alternative possible definition for split based on first

@[simp]
def split_NDEvent_fromFirst [Machine CTX M] (ev₁ : _NDEvent M α β) (ev₂ : _NDEvent M γ δ) : _NDEvent M (α × γ) (β × δ) :=
  Arrow.split_from_first (arrow_NDEvent M (fun (x, y) => (y, x)))
                         first_NDEvent ev₁ ev₂

instance [Machine CTX M]: Arrow (_NDEvent M) where
  arrow := arrow_NDEvent M
  split := split_NDEvent
  first := first_NDEvent

instance [Machine CTX M]: LawfulArrow (_NDEvent M) where
  arrow_id := by simp [Arrow.arrow]
  arrow_ext f := by simp [Arrow.arrow, Arrow.first]
                    funext m (x, z) ((y, z'), m')
                    simp
                    constructor
                    <;> (intro H ; simp [H])

  arrow_fun f g := by simp [Arrow.arrow]
                      funext m x (z, m')
                      simp
                      constructor
                      · intro H
                        exists (f x)
                        simp [H]
                      · intro Hex
                        cases Hex
                        case _ y H =>
                          simp [H]
  arrow_xcg ev g := by simp [Arrow.arrow, Arrow.first]
                       funext m (x, y₁) ((y₂, x'), m')
                       simp
                       constructor
                       · intro Hex
                         obtain ⟨⟨x'', z⟩, Hex⟩ := Hex
                         obtain ⟨m'', ⟨⟨H₁, H₂⟩, ⟨H₃,H₄⟩⟩⟩ := Hex
                         exists (y₂, y₁)
                         simp [*] at *
                         simp [H₁] at H₃
                         simp [H₁, H₃]
                       · intro Hex
                         obtain ⟨⟨y₃, y₄⟩, ⟨⟨H₁,H₂⟩,H₃,H₄⟩⟩ := Hex
                         exists (x, g y₁)
                         exists m
                         simp [*] at *
                         simp [H₂]

  arrow_unit ev := by simp [Arrow.arrow, Arrow.first]
                      funext m (x, y₁) (y₂, m')
                      simp
                      constructor
                      · intro Hex
                        obtain ⟨⟨y₃, y₄⟩, ⟨⟨H₁,H₂⟩,H₃⟩⟩ := Hex
                        exists x
                        exists m
                        simp [H₁, H₂, H₃]
                      · intro Hex
                        obtain ⟨x', Hex⟩  := Hex
                        obtain ⟨m'', ⟨H₁ , H₂⟩⟩ := Hex
                        exists (y₂, y₁)
                        simp
                        simp [H₁] at H₂
                        assumption

  arrow_assoc ev := by simp [Arrow.arrow, Arrow.first]
                       funext m ((x, z), t) ((y, z', t'), m')
                       simp
                       constructor
                       · intro Hex
                         obtain ⟨⟨⟨y',z''⟩, t''⟩, H⟩ := Hex
                         obtain ⟨⟨⟨H₁, H₂⟩, H₃⟩, ⟨H₄, H₅, H₆⟩⟩ := H
                         simp [*] at *
                         simp [H₅,H₂,H₄]
                         exists (x, z, t)
                         exists m
                         simp [H₁, H₃, H₆]
                       ·  intro Hex
                          obtain ⟨⟨x',z'',t''⟩, Hex⟩ := Hex
                          obtain ⟨m'', ⟨⟨H₁, H₂⟩, ⟨H₃,H₄⟩⟩⟩ := Hex
                          simp [*] at *
                          simp [H₁] at H₃
                          exists ((y, z), t)
                          simp [H₃]
                          simp [H₁, H₄]

/- Ordinary non-deterministic events -/

structure _NDEventPO [Machine CTX M] (ev : _NDEvent M α β) (kind : EventKind) where
  safety (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → ∀ y, ∀ m', ev.effect m x (y, m')
                 → Machine.invariant m'

  feasibility (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → ∃ y, ∃ m', ev.effect m x (y, m')

structure OrdinaryNDEvent (M) [Machine CTX M] (α) (β) extends _NDEvent M α β where
  po : _NDEventPO to_NDEvent  (EventKind.TransNonDet Convergence.Ordinary)

def OrdinaryNDEvent_fromOrdinaryEvent [Machine CTX M] (ev : OrdinaryEvent M α β) : OrdinaryNDEvent M α β :=
  let event := _NDEvent_fromEvent ev.to_Event
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

structure NDEventSpec (M) [Machine CTX M] (α) (β) where
  guard (m : M) (x : α) : Prop := True
  effect (m : M) (x : α) (_ : β × M) : Prop

  safety (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ y, ∀ m', effect m x (y, m')
                 → Machine.invariant m'

  feasibility (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∃ y, ∃ m', effect m x (y, m')

@[simp]
def _NDEvent_from_NDEventSpec [Machine CTX M] (ev : NDEventSpec M α β) : _NDEvent M α β :=
  { guard := ev.guard
    effect := ev.effect
  }

@[simp]
def newNDEvent {M} [Machine CTX M] (ev : NDEventSpec M α β) : OrdinaryNDEvent M α β :=
  let event := _NDEvent_from_NDEventSpec ev
  { guard := event.guard
    effect := event.effect
    po := { safety := fun m x => by simp
                                    intros Hinv Hgrd
                                    apply ev.safety <;> assumption
            feasibility := fun m x => by simp
                                         intros Hinv Hgrd
                                         apply ev.feasibility <;> assumption
    }
  }

structure InitNDEventSpec (M) [Machine CTX M] (α) (β) where
  guard (x : α) : Prop := True
  init (x : α) (_ : β × M) : Prop

  safety (x : α):
    guard x
    → ∀ y, ∀ m, init x (y, m)
                → Machine.invariant m

  feasibility (x : α):
    guard x
    → ∃ y, ∃ m, init x (y, m)

@[simp]
def NDEventSpec_from_InitNDEventSpec [Machine CTX M] (ev : InitNDEventSpec M α β) : NDEventSpec M α β :=
 {
  guard := fun m x => m = Machine.reset ∧ ev.guard x
  effect := fun _ x (y,m') => ev.init x (y, m')
  safety := fun m x => by simp ; intros ; apply ev.safety x <;> assumption
  feasibility := fun m x => by simp ; intros ; apply ev.feasibility x ; assumption
 }

 @[simp]
def newInitNDEvent {M} [Machine CTX M] (ev : InitNDEventSpec M α β) : OrdinaryNDEvent M α β :=
  newNDEvent (NDEventSpec_from_InitNDEventSpec ev)

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
                  cases ev
                  case mk _ev _po =>
                    simp
                    constructor
                    case left =>
                      have Hid_map := LawfulFunctor.id_map _ev
                      simp [Functor.map] at Hid_map
                      assumption
                    case right =>
                      apply cast_heq
                      simp
                      cases _ev
                      case _ evr eff =>
                        simp
                        cases evr
                        case mk grd =>
                          simp
                          congr
                          funext m z (x, m')
                          simp
                          constructor
                          · intro Heff
                            exists x
                          · intro Hex
                            obtain ⟨x', Heff⟩ := Hex
                            simp [Heff]

  comp_map g h ev := by simp [Functor.map]
                        cases ev
                        case mk _ev _po =>
                          simp
                          constructor
                          case left =>
                            have Hcm := LawfulFunctor.comp_map g h _ev
                            simp [Functor.map] at Hcm
                            assumption
                          case right =>
                            apply cast_heq
                            congr
                            funext m z (z', m')
                            simp
                            constructor
                            case _ =>
                              intro Hex
                              obtain ⟨y, Hex⟩ := Hex
                              obtain ⟨Hex, Hz'⟩ := Hex
                              rw [Hz']
                              obtain ⟨x, ⟨Heff, Hy⟩⟩ := Hex
                              rw [Hy]
                              exists x
                            case _ =>
                              intro Hex
                              obtain ⟨x, ⟨Heff, Hz'⟩⟩ := Hex
                              rw [Hz']
                              exists (g x)
                              simp
                              exists x

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
                                 clear Hdc'
                                 apply cast_heq
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
                                     intro (y,z')
                                     intro m'
                                     simp
                                     intros _ Heff
                                     apply Hsafe y m' Heff

        feasibility := fun m (x, z) => by simp [ev, StrongProfunctor.first']
                                          intro Hinv Hgrd
                                          have Hfeas := event.po.feasibility m x Hinv Hgrd
                                          obtain ⟨y, m', Hfeas⟩ := Hfeas
                                          exists (y,z)
                                          simp
                                          exists m'
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
                      apply cast_heq
                      simp [Hir]

  id_left ev := by simp
                   have Hil:= LawfulCategory.id_left ev.to_NDEvent
                   simp at Hil
                   cases ev
                   case mk _ po =>
                     simp [Hil]
                     apply cast_heq
                     simp [Hil]

  id_assoc ev₁ ev₂ ev₃ := by have Hia := LawfulCategory.id_assoc ev₁.to_NDEvent ev₂.to_NDEvent ev₃.to_NDEvent
                             simp [*] at *
                             cases ev₁
                             cases ev₂
                             cases ev₃
                             simp [Hia]
                             apply cast_heq
                             simp [Hia]

-- XXX: This axiom is required to obtain feasibility
axiom OrdinaryNDEvent_split_feasibility_ax {CTX} {M} [Machine CTX M] {α β α' β'} (ev₁ : _NDEvent M α β)  (ev₂ : _NDEvent M α' β')
  (m : M) (x : α) (x' : α'):
  (∃ y, ∃ m', ev₁.effect m x (y, m'))
  → (∃ y', ∃ m', ev₂.effect m x' (y', m'))
  → (∃ y, ∃ y', ∃ m', (Arrow.split ev₁ ev₂).effect m (x, x') ((y, y'), m'))

instance [Machine CTX M]: Arrow (OrdinaryNDEvent M) where

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
                                     intros Hinv Hgrd₁ _
                                     intro (y,y') m'
                                     simp
                                     intros Heff₁ _
                                     apply ev₁.po.safety m x Hinv Hgrd₁ y m' Heff₁

        -- this could be called "weak feasibility"
        feasibility := fun m (x, x') => by simp [Arrow.split, event]
                                           intros Hinv Hgrd₁ Hgrd₂
                                           have Hfeas₁ := ev₁.po.feasibility m x Hinv Hgrd₁
                                           have Hfeas₂ := ev₂.po.feasibility m x' Hinv Hgrd₂
                                           -- we cannot prove that m''= m' thus we rely on
                                           -- an dedicated axiom
                                           have Hax := (OrdinaryNDEvent_split_feasibility_ax ev₁.to_NDEvent ev₂.to_NDEvent m x x') Hfeas₁ Hfeas₂
                                           obtain ⟨y, y', m', Hax⟩ := Hax
                                           simp [Arrow.split] at Hax
                                           exists (y, y')
                                           exists m'
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
                                  intro (y',z) m'
                                  simp
                                  intro Heff _
                                  apply ev.po.safety m x Hinv Hgrd y' m' Heff

      feasibility := fun m (x,y) => by simp [event, Arrow.first]
                                       intros Hinv Hgrd
                                       have Hfeas := ev.po.feasibility m x Hinv Hgrd
                                       obtain ⟨y',m', Heff⟩ := Hfeas
                                       exists (y',y)
                                       simp
                                       exists m'
    }
  }

instance [Machine CTX M]: LawfulArrow (OrdinaryNDEvent M) where
  arrow_id := by simp [Arrow.arrow]

  arrow_ext {α β γ } f :=
      by have Hext := @LawfulArrow.arrow_ext (arr := _NDEvent M) _ _ α β γ f
         -- XXX : strange -this does not appear is expressed like this :
         -- have Hext := LawfulArrow.arrow_ext (arr := _NDEvent M) f
         simp [Arrow.arrow, Arrow.first]
         simp [Arrow.arrow, Arrow.first] at Hext
         simp [Hext]
         apply cast_heq
         simp [Hext]

  arrow_fun f g := by simp [Arrow.arrow]
                      have Hfun := LawfulArrow.arrow_fun (arr := _NDEvent M) f g
                      simp [Arrow.arrow] at Hfun
                      simp [Hfun]
                      apply cast_heq
                      simp [Hfun]

  arrow_xcg ev g := by simp [Arrow.arrow, Arrow.first, Arrow.split]
                       -- the following could be used, but is cumbersome to use ...
                       -- (and the alternative we use is ugly ...)
                       have Hxcg := LawfulArrow.arrow_xcg (arr:=_NDEvent M) ev.to_NDEvent g
                       simp [Arrow.arrow, Arrow.first, Arrow.split] at Hxcg
                       simp [Hxcg]
                       apply cast_heq
                       simp [Hxcg]

  arrow_unit ev := by simp [Arrow.arrow, Arrow.first]
                      -- we need to use the _NDEvent proof
                      have Hunit := LawfulArrow.arrow_unit (arr:=_NDEvent M) ev.to_NDEvent
                      simp [Arrow.first, Arrow.arrow] at Hunit
                      simp [Hunit]
                      apply cast_heq
                      simp [Hunit]

  arrow_assoc {α β γ δ} ev :=
      by simp [Arrow.arrow, Arrow.first]
         have Hasc := @LawfulArrow.arrow_assoc (arr:=_NDEvent M) _ _ α β γ δ ev.to_NDEvent
         simp [Arrow.arrow, Arrow.first] at Hasc
         simp [Hasc]
         apply cast_heq
         simp [Hasc]
