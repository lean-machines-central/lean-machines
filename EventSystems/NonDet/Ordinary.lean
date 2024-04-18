import EventSystems.Event.Basic
import EventSystems.NonDet.Basic

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

structure NDEventSpec' (M) [Machine CTX M] (α) where
  guard (m : M) (x : α) : Prop := True
  effect (m : M) (x : α) (m' : M) : Prop

  safety (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ m', effect m x m'
            → Machine.invariant m'

  feasibility (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∃ m', effect m x m'

@[simp]
def NDEventSpec'.toNDEventSpec [Machine CTX M] (ev : NDEventSpec' M α) : NDEventSpec M α Unit :=
  { guard := ev.guard
    effect := fun m x ((), m') => ev.effect m x m'
    safety := fun m x => by simp ; apply ev.safety
    feasibility := fun m x => by simp ; apply ev.feasibility
  }

@[simp]
def newNDEvent' {M} [Machine CTX M] (ev : NDEventSpec' M α) : OrdinaryNDEvent M α Unit :=
  newNDEvent ev.toNDEventSpec

structure NDEventSpec'' (M) [Machine CTX M] where
  guard (m : M) : Prop := True
  effect (m : M) (m' : M) : Prop

  safety (m : M):
    Machine.invariant m
    → guard m
    → ∀ m', effect m m'
            → Machine.invariant m'

  feasibility (m : M):
    Machine.invariant m
    → guard m
    → ∃ m', effect m m'

@[simp]
def NDEventSpec''.toNDEventSpec [Machine CTX M] (ev : NDEventSpec'' M) : NDEventSpec M Unit Unit :=
  { guard := fun m _ => ev.guard m
    effect := fun m () ((), m') => ev.effect m m'
    safety := fun m () => by simp ; apply ev.safety <;> assumption
    feasibility := fun m x => by simp ; apply ev.feasibility
  }

@[simp]
def newNDEvent'' {M} [Machine CTX M] (ev : NDEventSpec'' M) : OrdinaryNDEvent M Unit Unit :=
  newNDEvent ev.toNDEventSpec

/- Initialiazation events -/

structure _InitNDEventPO [Machine CTX M] (ev : _NDEvent M α β) (kind : EventKind) where
  safety (x : α):
    ev.guard Machine.reset x
    → ∀ y, ∀ m', ev.effect Machine.reset x (y, m')
                 → Machine.invariant m'

  feasibility (x : α):
    ev.guard Machine.reset x
    → ∃ y, ∃ m', ev.effect Machine.reset x (y, m')

structure InitNDEvent (M) [Machine CTX M] (α) (β) extends _NDEvent M α β where
  po : _InitNDEventPO to_NDEvent  EventKind.InitNonDet

@[simp]
def InitNDEvent.init [Machine CTX M]  (ev : InitNDEvent M α β) (x : α) (nxt : β × M) :=
  ev.effect Machine.reset x nxt

@[simp]
def InitNDEvent.init' [Machine CTX M] (ev : InitNDEvent M Unit β) (nxt: β × M) :=
  ev.init () nxt

@[simp]
def InitNDEvent.init'' [Machine CTX M] (ev : InitNDEvent M Unit Unit) (m : M) :=
  ev.init' ((), m)


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
def newInitNDEvent {M} [Machine CTX M] (ev : InitNDEventSpec M α β) : InitNDEvent M α β :=
  {
    guard := fun m x => m = Machine.reset ∧ ev.guard x
    effect := fun _ x (y, m') => ev.init x (y, m')
    po := {
      safety := fun x => by simp ; intros ; apply ev.safety x <;> assumption
      feasibility := fun x => by simp ; intros ; apply ev.feasibility x ; assumption
    }
  }

structure InitNDEventSpec' (M) [Machine CTX M] (α) where
  guard (x : α) : Prop := True
  init (x : α) (m : M) : Prop

  safety (x : α):
    guard x
    → ∀ m, init x m
           → Machine.invariant m

  feasibility (x : α):
    guard x
    → ∃ m, init x m

@[simp]
def InitNDEventSpec_from_InitNDEventSpec' [Machine CTX M] (ev : InitNDEventSpec' M α) : InitNDEventSpec M α Unit :=
  {
    guard := ev.guard
    init := fun x ((), m) => ev.init x m
    safety := fun x => by simp
                          intros Hgrd m Hini
                          apply ev.safety x Hgrd ; assumption
    feasibility := fun x => by simp
                               intros Hgrd
                               apply ev.feasibility x Hgrd
  }

@[simp]
def newInitNDEvent' [Machine CTX M] (ev : InitNDEventSpec' M α) : InitNDEvent M α Unit :=
  newInitNDEvent (InitNDEventSpec_from_InitNDEventSpec' ev)

structure InitNDEventSpec'' (M) [Machine CTX M] where
  guard : Prop := True
  init (m : M) : Prop

  safety:
    guard
    → ∀ m, init m
           → Machine.invariant m

  feasibility:
    guard
    → ∃ m, init m

@[simp]
def InitNDEventSpec_from_InitNDEventSpec'' [Machine CTX M] (ev : InitNDEventSpec'' M) : InitNDEventSpec M Unit Unit :=
  {
    guard := fun () => ev.guard
    init := fun () ((), m) => ev.init m
    safety := fun x => by simp
                          intros Hgrd m Hini
                          apply ev.safety Hgrd ; assumption
    feasibility := fun x => by simp
                               intros Hgrd
                               apply ev.feasibility Hgrd
  }

@[simp]
def newInitNDEvent'' [Machine CTX M] (ev : InitNDEventSpec'' M) : InitNDEvent M Unit Unit :=
  newInitNDEvent (InitNDEventSpec_from_InitNDEventSpec'' ev)

/- Algebraic properties -/

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
