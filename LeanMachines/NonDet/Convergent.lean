
import Mathlib.Order.RelClasses

import LeanMachines.Event.Convergent
import LeanMachines.NonDet.Basic
import LeanMachines.NonDet.Ordinary

/-!
## Convergent deterministic events

This module defines the anticipated and convergent properties
for non-deterministic events, cf. `Event.Convergent` module for
the deterministic case and common properties (e.g. what is convergence?).

-/

/-!
### Anticipated events
-/

/-- The internal representation of proof obligations for anticipated events. -/
structure _AnticipatedNDEventPO (v) [Preorder v] [instM:Machine CTX M] (ev : _NDEvent M α β) (kind : EventKind)
          extends _Variant v (instM:=instM), _NDEventPO ev kind  where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → ∀ y, ∀ m',  ev.effect m x (y, m')
                   → variant m' ≤ variant m

/-- The type of non-deterministic anticipated events.
It is an event for machine type `M` with input type `α` and output type `β`.
The non-increasing argument is based on the variant type `v` assumed
to be a preorder. -/
structure AnticipatedNDEvent (v) [Preorder v] (M) [Machine CTX M] (α) (β)
          extends (_NDEvent M α β)  where
  po : _AnticipatedNDEventPO v to_NDEvent (EventKind.TransNonDet Convergence.Anticipated)

/-- The "downgrading" of an anticipated event to an ordinary one. -/
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
private def AnticipatedNDEvent_fromOrdinary {v} [Preorder v] {M} [Machine CTX M] (ev : OrdinaryNDEvent M α β)
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

/-- The specification of a non-deterministic, anticipated event for machine `M`
with input type `α` and output type `β`. The non-increasing proof relies
 on a variant type `v` assumed to be a preorder.
Note that the guard, effect and safety PO of the event must be also
specified, as in the ordinary case (cf. `OrdinaryNDEventSpec`).
  -/
structure AnticipatedNDEventSpec (v) [Preorder v] {CTX} (M) [instM:Machine CTX M] (α) (β)
  extends _Variant v (instM:=instM), NDEventSpec M α β where
  /-- Proof obligation: the variant is non-increasing. -/
  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ y, ∀ m',  effect m x (y, m')
                   → variant m' ≤ variant m

/-- Construction of an anticipated non-deterministic event from a
`AnticipatedNDEventSpec` specification. -/
@[simp]
def newAnticipatedNDEvent [Preorder v] [Machine CTX M] (ev : AnticipatedNDEventSpec v M α β) : AnticipatedNDEvent v M α β :=
  AnticipatedNDEvent_fromOrdinary (newNDEvent ev.toNDEventSpec) ev.to_Variant.variant ev.nonIncreasing

/-- Variant of `AnticipatedNDEventSpec` with implicit `Unit` output type -/
structure AnticipatedNDEventSpec' (v) [Preorder v] {CTX} (M) [instM:Machine CTX M] (α)
  extends _Variant v (instM:=instM), NDEventSpec' M α where

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

/-- Variant of `newAnticipatedNDEvent` with implicit `Unit` output type -/
@[simp]
def newAnticipatedNDEvent' [Preorder v] [Machine CTX M] (ev : AnticipatedNDEventSpec' v M α) : AnticipatedNDEvent v M α Unit :=
  newAnticipatedNDEvent ev.toAnticipatedNDEventSpec

/-- Variant of `AnticipatedNDEventSpec` with implicit `Unit` input and output types -/
structure AnticipatedNDEventSpec'' (v) [Preorder v] {CTX} (M) [instM:Machine CTX M]
  extends _Variant v (instM:=instM), NDEventSpec'' M where

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

/-- Variant of `newAnticipatedNDEvent` with implicit `Unit` input and output types -/
@[simp]
def newAnticipatedNDEvent'' [Preorder v] [Machine CTX M] (ev : AnticipatedNDEventSpec'' v M) : AnticipatedNDEvent v M Unit Unit :=
  newAnticipatedNDEvent ev.toAnticipatedNDEventSpec

/-!
### Convergent events
-/

/-- The internal representation of proof obligations for convergent events. -/
structure _ConvergentNDEventPO (v) [Preorder v] [WellFoundedLT v] [Machine CTX M] (ev : _NDEvent M α β) (kind : EventKind)
          extends _AnticipatedNDEventPO v ev kind  where

  convergence (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → ∀ y, ∀ m',  ev.effect m x (y, m')
                   → variant m' < variant m

/-- The type of non-deterministic convergent events.
It is an event for machine type `M` with input type `α` and output type `β`.
The convergence argument is based on the variant type `v` assumed
to be a well-founded preorder. -/
structure ConvergentNDEvent (v) [Preorder v]  [WellFoundedLT v] (M) [Machine CTX M] (α) (β)
          extends (_NDEvent M α β)  where
  po : _ConvergentNDEventPO v to_NDEvent (EventKind.TransNonDet Convergence.Convergent)

/-- The "downgrading" of a convergent event to an anticipated one. -/
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


private def ConvergentNDEvent_fromOrdinary  {v} [Preorder v] [WellFoundedLT v] {M} [Machine CTX M] (ev : OrdinaryNDEvent M α β)
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

/-- The specification of a non-deterministic, convergent event for machine `M`
with input type `α` and output type `β`. The convergence proof relies
 on a variant type `v` assumed to be a well-founded preorder.
Note that the guard, action and safety PO of the event must be also
specified, as in the ordinary case (cf. `OrdinaryNDEventSpec`).
  -/
structure ConvergentNDEventSpec (v) [Preorder v] [WellFoundedLT v] (M) [instM:Machine CTX M] (α) (β)
  extends _Variant v (instM:=instM), NDEventSpec M α β where
  /-- Proof obligation: the variant is strictly decreasing. -/
  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ y, ∀ m',  effect m x (y, m')
                   → variant m' < variant m

/-- Construction of a convergent non-deterministic event from a
`ConvergentNDEventSpec` specification. -/
@[simp]
def newConvergentNDEvent {v} [Preorder v] [WellFoundedLT v] {M} [Machine CTX M] (ev : ConvergentNDEventSpec v M α β) : ConvergentNDEvent v M α β :=
  ConvergentNDEvent_fromOrdinary (newNDEvent ev.toNDEventSpec) ev.to_Variant.variant ev.convergence

@[simp]
private def ConvergentNDEvent_fromAnticipated {v} [Preorder v] [WellFoundedLT v] {M} [Machine CTX M] (ev : AnticipatedNDEvent v M α β)
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

/-- Variant of `ConvergentNDEventSpec` with implicit `Unit` output type -/
structure ConvergentNDEventSpec' (v) [Preorder v] [WellFoundedLT v] (M) [instM:Machine CTX M] (α)
  extends _Variant v (instM:=instM), NDEventSpec' M α where

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

/-- Variant of `newConvergentNDEvent` with implicit `Unit` output type -/
@[simp]
def newConvergentNDEvent' [Preorder v] [WellFoundedLT v] [Machine CTX M] (ev : ConvergentNDEventSpec' v M α) : ConvergentNDEvent v M α Unit :=
  newConvergentNDEvent ev.toConvergentNDEventSpec

/-- Variant of `ConvergentNDEventSpec` with implicit `Unit` input and output types -/
structure ConvergentNDEventSpec'' (v) [Preorder v] [WellFoundedLT v] (M) [instM:Machine CTX M]
  extends _Variant v (instM:=instM), NDEventSpec'' M where

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

/-- Variant of `newConvergentEvent` with implicit `Unit` input and output types -/
@[simp]
def newConvergentNDEvent'' [Preorder v] [WellFoundedLT v] [Machine CTX M] (ev : ConvergentNDEventSpec'' v M) : ConvergentNDEvent v M Unit Unit :=
  newConvergentNDEvent ev.toConvergentNDEventSpec

/-!
## Algebraic properties

The following instantiate various algebraic structures for anticipated
and convergent non-deterministic events (experimental, not documented).

-/

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

/- TODO : issue with dependent equality, should be workable ...
instance [Preorder v] [Machine CTX M] : LawfulFunctor (AnticipatedNDEvent v M γ) where
  map_const := by simp [Functor.map, Functor.mapConst]
  id_map ev := by simp [Functor.map]
                  cases ev
                  case mk _ev po =>
                    simp [Functor.map]
                    cases po
                    case mk _v _po _ni =>
                      -- this can be maybe work by specifying the cast ?
                      apply heq_of_cast_eq
                      sorry

  comp_map g h ev := by simp [Functor.map]
                        have hcmp := LawfulFunctor.comp_map g h ev.to_NDEvent
                        simp [Functor.map] at hcmp
                        constructor
                        · assumption
                        -- same
                        sorry
... -/


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

/- TODO : issue with dependent equality, should be workable ...
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
-/

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


/- TODO : issue with dependent equality, should be workable ...
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
-/

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

-- TODO: lawful strong profunctor
-- instance [Preorder v] [Machine CTX M] : LawfulStrongProfunctor (AnticipatedNDEvent v M) where

instance [Preorder v] [WellFoundedLT v] [Machine CTX M] : Profunctor (ConvergentNDEvent v M) where
  dimap {α β} {γ δ} (f : β → α) (g : γ → δ) (ev : ConvergentNDEvent v M α γ) : ConvergentNDEvent v M β δ :=
  let ev' := ConvergentNDEvent_from_CoConvergentNDEvent (ContravariantFunctor.contramap f (CoConvergentNDEvent_from_ConvergentNDEvent ev))
  g <$> ev'


/- TODO : issue with dependent equality, should be workable ...
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
-/

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

-- TODO: lawful strong profunctor
-- instance [Preorder v] [WellFoundedLT v] [Machine CTX M] : LawfulStrongProfunctor (ConvergentNDEvent v M) where
