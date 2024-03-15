
import EventSystems.Classes
import EventSystems.Basic

structure _NDEvent (M) [Machine CTX M] (α) (β : Type)
  extends _EventRoot M α where

  effect: M → α → (β × M) → Prop

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


-- There are two possible, distinct contravariant functors
-- for non-deterministic events.

-- The first operates on the output, hence it cannot be use
-- in a profunctor context
instance [Machine CTX M] : Contravariant (_NDEvent M γ) where
  contramap f ev :=
  {
    guard := ev.guard
    effect := fun m x (y, m') => ev.effect m x ((f y), m')
  }

instance [Machine CTX M] : LawfullContravariant (_NDEvent M β) where
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


instance [Machine CTX M] : Contravariant (_CoNDEvent M γ) where
  contramap f ev :=
  {
     guard := fun m x => ev.guard m (f x)
     effect := fun m x (y, m')  => ev.effect m (f x) (y, m')
  }

instance [Machine CTX M] : LawfullContravariant (_CoNDEvent M γ) where
  cmap_id _ := rfl
  cmap_comp _ _ := rfl

-- There is a unique possible profunctor instance
instance [Machine CTX M] : Profunctor (_NDEvent M) where
  dimap {α β} {γ δ} (f : β → α) (g : γ → δ) (ev : _NDEvent M α γ) : _NDEvent M β δ :=
  let ev' := NDEvent_from_CoNDEvent (Contravariant.contramap f (CoNDEvent_from_NDEvent ev))
  g <$> ev'

instance [Machine CTX M] : LawfulProfunctor (_NDEvent M) where
  dimap_id := by simp [Profunctor.dimap, Contravariant.contramap]
                 exact fun {α β} => rfl
  dimap_comp f f' g g' := by simp [Profunctor.dimap, Contravariant.contramap, Functor.map]
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
def arrow_NDEvent [Machine CTX M] (f : α → β) : _NDEvent M α β :=
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

instance [Machine CTX M]: Arrow (_NDEvent M) where
  arrow := arrow_NDEvent
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
