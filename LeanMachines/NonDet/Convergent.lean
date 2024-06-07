
import Mathlib.Order.RelClasses

import LeanMachines.Event.Convergent
import LeanMachines.NonDet.Basic
import LeanMachines.NonDet.Ordinary

/- Anticipated events -/

structure _AnticipatedNDEventPO (v) [Preorder v] [Machine CTX M] (ev : _NDEvent M α β) (kind : EventKind)
          extends _Variant v, _NDEventPO ev kind  where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → ∀ y, ∀ m',  ev.effect m x (y, m')
                   → variant m' ≤ variant m

structure AnticipatedNDEvent (v) [Preorder v] (M) [Machine CTX M] (α) (β)
          extends (_NDEvent M α β)  where
  po : _AnticipatedNDEventPO v to_NDEvent (EventKind.TransNonDet Convergence.Anticipated)

@[simp]
def AnticipatedNDEvent.toOrdinaryNDEvent [Preorder v] [Machine CTX M]
  (ev : AnticipatedNDEvent v M α β) : OrdinaryNDEvent M α β :=
  {
    to_NDEvent := ev.to_NDEvent
    po := {
      safety := ev.po.safety
      feasibility := ev.po.feasibility
    }
  }

@[simp]
def AnticipatedNDEvent_fromOrdinary {v} [Preorder v] {M} [Machine CTX M] (ev : OrdinaryNDEvent M α β)
  (variant : M → v)
  (Hnincr: ∀ (m : M) (x : α),
    Machine.invariant m
    → ev.guard m x
    → ∀ y, ∀ m',  ev.effect m x (y, m')
                   → variant m' ≤ variant m) : AnticipatedNDEvent v M α β :=
  {
    guard := ev.guard
    effect := ev.effect
    po := {
      safety := ev.po.safety
      feasibility := ev.po.feasibility
      variant := variant
      nonIncreasing := Hnincr
    }
  }

structure AnticipatedNDEventSpec (v) [Preorder v] {CTX} (M) [Machine CTX M] (α) (β)
  extends _Variant v, NDEventSpec M α β where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ y, ∀ m',  effect m x (y, m')
                   → variant m' ≤ variant m

@[simp]
def newAnticipatedNDEvent [Preorder v] [Machine CTX M] (ev : AnticipatedNDEventSpec v M α β) : AnticipatedNDEvent v M α β :=
  AnticipatedNDEvent_fromOrdinary (newNDEvent ev.toNDEventSpec) ev.to_Variant.variant ev.nonIncreasing

structure AnticipatedNDEventSpec' (v) [Preorder v] {CTX} (M) [Machine CTX M] (α)
  extends _Variant v, NDEventSpec' M α where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ m',  effect m x m'
             → variant m' ≤ variant m

@[simp]
def AnticipatedNDEventSpec'.toAnticipatedNDEventSpec [Preorder v] [Machine CTX M]
  (ev : AnticipatedNDEventSpec' v M α) : AnticipatedNDEventSpec v M α Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec
    variant := ev.variant
    nonIncreasing := fun m x => by simp
                                   intros Hinv Hgrd m' Heff
                                   apply ev.nonIncreasing m x Hinv Hgrd ; assumption
  }

@[simp]
def newAnticipatedNDEvent' [Preorder v] [Machine CTX M] (ev : AnticipatedNDEventSpec' v M α) : AnticipatedNDEvent v M α Unit :=
  newAnticipatedNDEvent ev.toAnticipatedNDEventSpec

structure AnticipatedNDEventSpec'' (v) [Preorder v] {CTX} (M) [Machine CTX M]
  extends _Variant v, NDEventSpec'' M where

  nonIncreasing (m : M):
    Machine.invariant m
    → guard m
    → ∀ m',  effect m m'
             → variant m' ≤ variant m

@[simp]
def AnticipatedNDEventSpec''.toAnticipatedNDEventSpec [Preorder v] [Machine CTX M]
  (ev : AnticipatedNDEventSpec'' v M) : AnticipatedNDEventSpec v M Unit Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec
    variant := ev.variant
    nonIncreasing := fun m x => by simp
                                   intros Hinv Hgrd m' Heff
                                   apply ev.nonIncreasing m Hinv Hgrd ; assumption
  }

@[simp]
def newAnticipatedNDEvent'' [Preorder v] [Machine CTX M] (ev : AnticipatedNDEventSpec'' v M) : AnticipatedNDEvent v M Unit Unit :=
  newAnticipatedNDEvent ev.toAnticipatedNDEventSpec

/- Convergent events -/

structure _ConvergentNDEventPO (v) [Preorder v] [WellFoundedLT v] [Machine CTX M] (ev : _NDEvent M α β) (kind : EventKind)
          extends _AnticipatedNDEventPO v ev kind  where

  convergence (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → ∀ y, ∀ m',  ev.effect m x (y, m')
                   → variant m' < variant m

structure ConvergentNDEvent (v) [Preorder v]  [WellFoundedLT v] (M) [Machine CTX M] (α) (β)
          extends (_NDEvent M α β)  where
  po : _ConvergentNDEventPO v to_NDEvent (EventKind.TransNonDet Convergence.Convergent)

@[simp]
def ConvergentNDEvent.toAnticipatedNDEvent [Preorder v] [WellFoundedLT v] [Machine CTX M]
  (ev : ConvergentNDEvent v M α β) : AnticipatedNDEvent v M α β :=
  {
    to_NDEvent := ev.to_NDEvent
    po := {
      safety := ev.po.safety
      feasibility := ev.po.feasibility
      variant := ev.po.variant
      nonIncreasing := ev.po.nonIncreasing
    }
  }


def ConvergentNDEvent_fromOrdinary  {v} [Preorder v] [WellFoundedLT v] {M} [Machine CTX M] (ev : OrdinaryNDEvent M α β)
  (variant : M → v)
  (Hconv: ∀ (m : M) (x : α),
    Machine.invariant m
    → ev.guard m x
    → ∀ y, ∀ m',  ev.effect m x (y, m')
                   → variant m' < variant m)
 : ConvergentNDEvent v M α β :=
 {
  guard := ev.guard
  effect := ev.effect
  po := {
    safety := ev.po.safety
    feasibility := ev.po.feasibility
    variant := variant
    nonIncreasing := fun m x => by simp
                                   intros Hinv Hgrd
                                   intros y m'
                                   have Hconv' := Hconv m x Hinv Hgrd y m'
                                   intro Heff
                                   apply le_of_lt
                                   exact Hconv' Heff
    convergence := Hconv
  }
 }

structure ConvergentNDEventSpec (v) [Preorder v] [WellFoundedLT v] (M) [Machine CTX M] (α) (β)
  extends _Variant v, NDEventSpec M α β where

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ y, ∀ m',  effect m x (y, m')
                   → variant m' < variant m

@[simp]
def newConvergentNDEvent {v} [Preorder v] [WellFoundedLT v] {M} [Machine CTX M] (ev : ConvergentNDEventSpec v M α β) : ConvergentNDEvent v M α β :=
  ConvergentNDEvent_fromOrdinary (newNDEvent ev.toNDEventSpec) ev.to_Variant.variant ev.convergence

@[simp]
def ConvergentNDEvent_fromAnticipated {v} [Preorder v] [WellFoundedLT v] {M} [Machine CTX M] (ev : AnticipatedNDEvent v M α β)
    (hconv : (m : M) → (x : α)
    → Machine.invariant m
    → ev.guard m x
    → ∀ y, ∀ m',  ev.effect m x (y, m')
                   → ev.po.variant m' < ev.po.variant m) : ConvergentNDEvent v M α β :=
  {
    guard := ev.guard
    effect := ev.effect
    po := {
      safety := ev.po.safety
      feasibility := ev.po.feasibility
      variant := ev.po.variant
      nonIncreasing := ev.po.nonIncreasing
      convergence := hconv
    }
  }

structure ConvergentNDEventSpec' (v) [Preorder v] [WellFoundedLT v] (M) [Machine CTX M] (α)
  extends _Variant v, NDEventSpec' M α where

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ m',  effect m x m'
             → variant m' < variant m

@[simp]
def ConvergentNDEventSpec'.toConvergentNDEventSpec [Preorder v] [WellFoundedLT v] {M} [Machine CTX M]
  (ev : ConvergentNDEventSpec' v M α) : ConvergentNDEventSpec v M α Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec
    variant := ev.variant
    convergence := fun m x => by simp
                                 intros Hinv Hgrd m' Heff
                                 apply ev.convergence <;> assumption
  }

@[simp]
def newConvergentNDEvent' [Preorder v] [WellFoundedLT v] [Machine CTX M] (ev : ConvergentNDEventSpec' v M α) : ConvergentNDEvent v M α Unit :=
  newConvergentNDEvent ev.toConvergentNDEventSpec

structure ConvergentNDEventSpec'' (v) [Preorder v] [WellFoundedLT v] (M) [Machine CTX M]
  extends _Variant v, NDEventSpec'' M where

  convergence (m : M):
    Machine.invariant m
    → guard m
    → ∀ m',  effect m m'
             → variant m' < variant m

@[simp]
def ConvergentNDEventSpec''.toConvergentNDEventSpec [Preorder v] [WellFoundedLT v] [Machine CTX M]
  (ev : ConvergentNDEventSpec'' v M) : ConvergentNDEventSpec v M Unit Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec
    variant := ev.variant
    convergence := fun m x => by simp
                                 intros Hinv Hgrd m' Heff
                                 apply ev.convergence <;> assumption
  }

@[simp]
def newConvergentNDEvent'' [Preorder v] [WellFoundedLT v] [Machine CTX M] (ev : ConvergentNDEventSpec'' v M) : ConvergentNDEvent v M Unit Unit :=
  newConvergentNDEvent ev.toConvergentNDEventSpec

/- Algebraic properties -/

/- Functor -/

instance [Preorder v] [Machine CTX M] : Functor (AnticipatedNDEvent v M γ) where
  map f ev := {
    to_NDEvent := f <$> ev.to_NDEvent
    po := {
      safety := fun m x => by simp [Functor.map]
                              intros Hinv Hgrd _ m' x' Heff _
                              apply ev.po.safety m x Hinv Hgrd x' m' Heff

      feasibility := fun m x => by simp [Functor.map]
                                   intros Hinv Hgrd
                                   have Hfeas := ev.po.feasibility m x Hinv Hgrd
                                   obtain ⟨y, m', Heff⟩ := Hfeas
                                   exists (f y) ; exists m' ; exists y

      variant := ev.po.variant

      nonIncreasing := fun m x => by simp [Functor.map]
                                     intros Hinv Hgrd _ m' x' Heff _
                                     have Hni := ev.po.nonIncreasing m x Hinv Hgrd x' m'
                                     apply Hni ; assumption

    }
  }

instance [Preorder v] [Machine CTX M] : LawfulFunctor (AnticipatedNDEvent v M γ) where
  map_const := by simp [Functor.map, Functor.mapConst]
  id_map ev := by cases ev
                  case mk _ev po =>
                    simp [Functor.map]
                    sorry -- don't know how to finish this
  comp_map g h ev := by simp [Functor.map]
                        have hcmp := LawfulFunctor.comp_map g h ev.to_NDEvent
                        simp [Functor.map] at hcmp
                        constructor
                        · assumption
                        -- same
                        sorry


instance [Preorder v] [WellFoundedLT v] [Machine CTX M] : Functor (ConvergentNDEvent v M γ) where
  map f ev := {
    to_NDEvent := f <$> ev.to_NDEvent
    po := {
      safety := fun m x => by simp [Functor.map]
                              intros Hinv Hgrd _ m' x' Heff _
                              apply ev.po.safety m x Hinv Hgrd x' m' Heff

      feasibility := fun m x => by simp [Functor.map]
                                   intros Hinv Hgrd
                                   have Hfeas := ev.po.feasibility m x Hinv Hgrd
                                   obtain ⟨y, m', Heff⟩ := Hfeas
                                   exists (f y) ; exists m' ; exists y

      variant := ev.po.variant

      nonIncreasing := fun m x => by simp [Functor.map]
                                     intros Hinv Hgrd _ m' x' Heff _
                                     have Hni := ev.po.nonIncreasing m x Hinv Hgrd x' m'
                                     apply Hni ; assumption

      convergence := fun m x => by simp [Functor.map]
                                   intros Hinv Hgrd _ m' x' Heff _
                                   have Hcv := ev.po.convergence m x Hinv Hgrd x' m'
                                   apply Hcv ; assumption

    }
  }

instance [Preorder v] [WellFoundedLT v] [Machine CTX M] : LawfulFunctor (ConvergentNDEvent v M γ) where
  map_const := by simp [Functor.map, Functor.mapConst]
  id_map ev := by cases ev
                  case mk _ev po =>
                    simp [Functor.map]
                    sorry -- don't know how to finish this
  comp_map g h ev := by simp [Functor.map]
                        have hcmp := LawfulFunctor.comp_map g h ev.to_NDEvent
                        simp [Functor.map] at hcmp
                        constructor
                        · assumption
                        -- same
                        sorry

abbrev CoAnticipatedNDEvent (v) [Preorder v] (M) [Machine CTX M] (α) (β) := AnticipatedNDEvent v M β α

@[simp]
def CoAnticipatedNDEvent_from_AnticipatedNDEvent [Preorder v] [Machine CTX M] (ev : AnticipatedNDEvent v M α β) : CoAnticipatedNDEvent v M β α :=
 ev

@[simp]
def AnticipatedNDEvent_from_CoAnticipatedNDEvent [Preorder v] [Machine CTX M] (ev : CoAnticipatedNDEvent v M β α) : AnticipatedNDEvent v M α β :=
 ev

instance [Preorder v] [Machine CTX M] : ContravariantFunctor (CoAnticipatedNDEvent v M γ) where
  contramap {α β} (f : β → α) event :=
  let ev : _CoNDEvent M γ β := ContravariantFunctor.contramap f event.to_NDEvent
  {
     to_NDEvent := ev
     po := {
      safety := fun m x => by revert ev
                              cases event
                              case mk _ev po =>
                                simp [ContravariantFunctor.contramap]
                                intros Hinv Hgrd y m' Heff
                                apply po.safety m (f x) Hinv Hgrd y m' Heff
      feasibility := fun m x => by intro Hinv
                                   revert ev
                                   cases event
                                   case mk _ev po =>
                                     simp [ContravariantFunctor.contramap]
                                     apply po.feasibility m (f x) Hinv

      variant := event.po.variant

      nonIncreasing := fun m x => by simp
                                     intro Hinv
                                     revert ev
                                     cases event
                                     case mk _ev po =>
                                       simp [ContravariantFunctor.contramap]
                                       intros Hgrd z m' Heff
                                       have Hni := po.nonIncreasing m (f x) Hinv Hgrd z m'
                                       apply Hni ; assumption

     }
  }

instance [Preorder v] [WellFoundedLT v] [Machine CTX M] : LawfullContravariantFunctor (CoAnticipatedNDEvent v M γ) where
  cmap_id _ := rfl
  cmap_comp _ _ := rfl

abbrev CoConvergentNDEvent (v) [Preorder v] [WellFoundedLT v]  (M) [Machine CTX M] (α) (β) := ConvergentNDEvent v M β α

@[simp]
def CoConvergentNDEvent_from_ConvergentNDEvent [Preorder v] [WellFoundedLT v] [Machine CTX M] (ev : ConvergentNDEvent v M α β) : CoConvergentNDEvent v M β α :=
 ev

@[simp]
def ConvergentNDEvent_from_CoConvergentNDEvent [Preorder v] [WellFoundedLT v] [Machine CTX M] (ev : CoConvergentNDEvent v M β α) : ConvergentNDEvent v M α β :=
 ev

instance [Preorder v] [WellFoundedLT v]  [Machine CTX M] : ContravariantFunctor (CoConvergentNDEvent v M γ) where
  contramap {α β} (f : β → α) event :=
  let ev : _CoNDEvent M γ β := ContravariantFunctor.contramap f event.to_NDEvent
  {
     to_NDEvent := ev
     po := {
      safety := fun m x => by revert ev
                              cases event
                              case mk _ev po =>
                                simp [ContravariantFunctor.contramap]
                                intros Hinv Hgrd y m' Heff
                                apply po.safety m (f x) Hinv Hgrd y m' Heff
      feasibility := fun m x => by intro Hinv
                                   revert ev
                                   cases event
                                   case mk _ev po =>
                                     simp [ContravariantFunctor.contramap]
                                     apply po.feasibility m (f x) Hinv

      variant := event.po.variant

      nonIncreasing := fun m x => by simp
                                     intro Hinv
                                     revert ev
                                     cases event
                                     case mk _ev po =>
                                       simp [ContravariantFunctor.contramap]
                                       intros Hgrd z m' Heff
                                       have Hni := po.nonIncreasing m (f x) Hinv Hgrd z m'
                                       apply Hni ; assumption

      convergence := fun m x => by simp
                                   intro Hinv
                                   revert ev
                                   cases event
                                   case mk _ev po =>
                                     simp [ContravariantFunctor.contramap]
                                     intros Hgrd z m' Heff
                                     have Hcv := po.convergence m (f x) Hinv Hgrd z m'
                                     apply Hcv ; assumption

     }
  }

instance [Preorder v] [WellFoundedLT v] [Machine CTX M] : LawfullContravariantFunctor (CoConvergentNDEvent v M γ) where
  cmap_id _ := rfl
  cmap_comp _ _ := rfl

/- Profunctor -/

instance [Preorder v] [Machine CTX M] : Profunctor (AnticipatedNDEvent v M) where
  dimap {α β} {γ δ} (f : β → α) (g : γ → δ) (ev : AnticipatedNDEvent v M α γ) : AnticipatedNDEvent v M β δ :=
  let ev' := AnticipatedNDEvent_from_CoAnticipatedNDEvent (ContravariantFunctor.contramap f (CoAnticipatedNDEvent_from_AnticipatedNDEvent ev))
  g <$> ev'


instance  [Preorder v] [Machine CTX M] : LawfulProfunctor (AnticipatedNDEvent v M) where
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
                                 -- cast_heq does not work so I'm stuck ...
                                 sorry

instance [Preorder v] [Machine CTX M] : StrongProfunctor (AnticipatedNDEvent v M) where
  first' {α β γ} (event : AnticipatedNDEvent v M α β): AnticipatedNDEvent v M (α × γ) (β × γ) :=
    let ev : _NDEvent M (α × γ) (β × γ) := StrongProfunctor.first' event.to_NDEvent
    {
      guard := ev.guard
      effect := ev.effect
      po := {
        safety := fun m (x, z) => by simp [ev, StrongProfunctor.first']
                                     intros Hinv Hgrd
                                     have Hsafe := event.po.safety m x Hinv Hgrd
                                     intros y _ m' _ Heff
                                     apply Hsafe y m' Heff

        feasibility := fun m (x, z) => by simp [ev, StrongProfunctor.first']
                                          intro Hinv Hgrd
                                          have Hfeas := event.po.feasibility m x Hinv Hgrd
                                          obtain ⟨y, m', Hfeas⟩ := Hfeas
                                          exists y
                                          exists m'

        variant := event.po.variant

        nonIncreasing := fun m (x, z) => by simp [ev, StrongProfunctor.first']
                                            intros Hinv Hgrd
                                            intros y _ m' _ Heff
                                            have Hni := event.po.nonIncreasing m x Hinv Hgrd y m'
                                            apply Hni
                                            assumption

      }
    }

instance [Preorder v] [Machine CTX M] : LawfulStrongProfunctor (AnticipatedNDEvent v M) where

instance [Preorder v] [WellFoundedLT v] [Machine CTX M] : Profunctor (ConvergentNDEvent v M) where
  dimap {α β} {γ δ} (f : β → α) (g : γ → δ) (ev : ConvergentNDEvent v M α γ) : ConvergentNDEvent v M β δ :=
  let ev' := ConvergentNDEvent_from_CoConvergentNDEvent (ContravariantFunctor.contramap f (CoConvergentNDEvent_from_ConvergentNDEvent ev))
  g <$> ev'


instance  [Preorder v] [WellFoundedLT v] [Machine CTX M] : LawfulProfunctor (ConvergentNDEvent v M) where
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
                                 -- cast_heq does not work so I'm stuck ...
                                 sorry

instance [Preorder v] [WellFoundedLT v] [Machine CTX M] : StrongProfunctor (ConvergentNDEvent v M) where
  first' {α β γ} (event : ConvergentNDEvent v M α β): ConvergentNDEvent v M (α × γ) (β × γ) :=
    let ev : _NDEvent M (α × γ) (β × γ) := StrongProfunctor.first' event.to_NDEvent
    {
      guard := ev.guard
      effect := ev.effect
      po := {
        safety := fun m (x, z) => by simp [ev, StrongProfunctor.first']
                                     intros Hinv Hgrd
                                     have Hsafe := event.po.safety m x Hinv Hgrd
                                     intros y _ m' _ Heff
                                     apply Hsafe y m' Heff

        feasibility := fun m (x, z) => by simp [ev, StrongProfunctor.first']
                                          intro Hinv Hgrd
                                          have Hfeas := event.po.feasibility m x Hinv Hgrd
                                          obtain ⟨y, m', Hfeas⟩ := Hfeas
                                          exists y
                                          exists m'

        variant := event.po.variant

        nonIncreasing := fun m (x, z) => by simp [ev, StrongProfunctor.first']
                                            intros Hinv Hgrd
                                            intros y _ m' _ Heff
                                            have Hni := event.po.nonIncreasing m x Hinv Hgrd y m'
                                            apply Hni
                                            assumption

        convergence := fun m (x, z) => by simp [ev, StrongProfunctor.first']
                                          intros Hinv Hgrd
                                          intros y _ m' _ Heff
                                          have Hcv := event.po.convergence m x Hinv Hgrd y m'
                                          apply Hcv
                                          assumption

      }
    }

instance [Preorder v] [WellFoundedLT v] [Machine CTX M] : LawfulStrongProfunctor (ConvergentNDEvent v M) where
