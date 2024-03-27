
import Mathlib.Order.RelClasses

import EventSystems.Basic

structure _Variant (v) [Preorder v] [Machine CTX M] where
  variant : M → v

/- Anticipated events -/

structure _AnticipatedEventPO (v) [Preorder v] [Machine CTX M] (ev : _Event M α β) (kind : EventKind)
          extends _Variant v, _EventPO ev kind  where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → let (_, m') := ev.action m x
      variant m' ≤ variant m

structure AnticipatedEvent (v) [Preorder v] (M) [Machine CTX M] (α) (β)
          extends (_Event M α β)  where
  po : _AnticipatedEventPO v to_Event (EventKind.TransDet Convergence.Anticipated)

@[simp]
def AnticipatedEvent_fromOrdinary {v} [Preorder v] {M} [Machine CTX M] (ev : OrdinaryEvent M α β)
  (variant : M → v)
  (Hnincr: ∀ (m : M) (x : α),
    Machine.invariant m
    → ev.guard m x
    → let (_, m') := ev.action m x
      variant m' ≤ variant m) : AnticipatedEvent v M α β :=
  {
    guard := ev.guard
    action := ev.action
    po := {
      safety := ev.po.safety
      variant := variant
      nonIncreasing := Hnincr
    }
  }

structure AnticipatedEventSpec (v) [Preorder v] {CTX} (M) [Machine CTX M] (α) (β)
  extends _Variant v, EventSpec M α β where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := (action m x).2
      variant m' ≤ variant m

@[simp]
def newAnticipatedEvent {v} [Preorder v] {M} [Machine CTX M] (ev : AnticipatedEventSpec v M α β) : AnticipatedEvent v M α β :=
  AnticipatedEvent_fromOrdinary (newEvent ev.toEventSpec) ev.to_Variant.variant ev.nonIncreasing

/- Convergent events -/

structure _ConvergentEventPO (v) [Preorder v] [WellFoundedLT v] [Machine CTX M] (ev : _Event M α β) (kind : EventKind)
          extends _AnticipatedEventPO v ev kind  where

  convergence (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → let (_, m') := ev.action m x
      variant m' < variant m

structure ConvergentEvent (v) [Preorder v]  [WellFoundedLT v] (M) [Machine CTX M] (α) (β)
          extends (_Event M α β)  where
  po : _ConvergentEventPO v to_Event (EventKind.TransDet Convergence.Convergent)

def ConvergentEvent_fromOrdinary  {v} [Preorder v] [WellFoundedLT v] {M} [Machine CTX M] (ev : OrdinaryEvent M α β)
  (variant : M → v)
  (Hconv: ∀ (m : M) (x : α),
    Machine.invariant m
    → ev.guard m x
    → let m' := (ev.action m x).2
      variant m' < variant m)
 : ConvergentEvent v M α β :=
 {
  guard := ev.guard
  action := ev.action
  po := {
    safety := ev.po.safety
    variant := variant
    nonIncreasing := fun m x => by simp
                                   intros Hinv Hgrd
                                   have Hconv' := Hconv m x Hinv Hgrd
                                   apply le_of_lt
                                   exact Hconv'
    convergence := Hconv
  }
 }

structure ConvergentEventSpec (v) [Preorder v] [WellFoundedLT v] (M) [Machine CTX M] (α) (β)
  extends _Variant v, EventSpec M α β where

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := (action m x).2
      variant m' < variant m

@[simp]
def newConvergentEvent {v} [Preorder v] [WellFoundedLT v] {M} [Machine CTX M] (ev : ConvergentEventSpec v M α β) : ConvergentEvent v M α β :=
  ConvergentEvent_fromOrdinary (newEvent ev.toEventSpec) ev.to_Variant.variant ev.convergence

@[simp]
def ConvergentEvent_fromAnticipated {v} [Preorder v] [WellFoundedLT v] {M} [Machine CTX M] (ev : AnticipatedEvent v M α β)
    (hconv : (m : M) → (x : α)
    → Machine.invariant m
    → ev.guard m x
    → let m' := (ev.action m x).2
      ev.po.variant m' < ev.po.variant m) : ConvergentEvent v M α β :=
  {
    guard := ev.guard
    action := ev.action
    po := {
      safety := ev.po.safety
      variant := ev.po.variant
      nonIncreasing := ev.po.nonIncreasing
      convergence := hconv
    }
  }

/- Algebraic properties -/

@[simp]
def mapAnticipatedEvent [Preorder v] [Machine CTX M] (f : α → β) (ev : AnticipatedEvent v M γ α) : AnticipatedEvent v M γ β :=
  newAnticipatedEvent {
    guard := ev.guard
    action := fun m x => let (y, m') := ev.action m x
                         (f y, m')
    safety :=  ev.po.safety
    variant := ev.po.variant
    nonIncreasing := ev.po.nonIncreasing
  }

instance [Preorder v] [Machine CTX M] : Functor (AnticipatedEvent v M γ) where
  map := mapAnticipatedEvent

instance [Preorder v] [Machine CTX M] : LawfulFunctor (AnticipatedEvent v M γ) where
  map_const := rfl
  id_map := by intros ; rfl
  comp_map := by intros ; rfl

def mapConvergentEvent [Preorder v] [WellFoundedLT v] [Machine CTX M] (f : α → β) (ev : ConvergentEvent v M γ α) : ConvergentEvent v M γ β :=
  newConvergentEvent {
    guard := ev.guard
    action := fun m x => let (y, m') := ev.action m x
                         (f y, m')
    safety :=  ev.po.safety
    variant := ev.po.variant
    convergence := ev.po.convergence
  }

instance [Preorder v] [WellFoundedLT v] [Machine CTX M] : Functor (ConvergentEvent v M γ) where
  map := mapConvergentEvent

instance [Preorder v] [WellFoundedLT v] [Machine CTX M] : LawfulFunctor (ConvergentEvent v M γ) where
  map_const := rfl
  id_map := by intros ; rfl
  comp_map := by intros ; rfl

/- Contravariant functor -/

abbrev CoAnticipatedEvent (v) [Preorder v] (M) [Machine CTX M] (α) (β) :=
   AnticipatedEvent v M β α

@[simp]
def AnticipatedEvent_from_CoAnticipatedEvent [Preorder v] [Machine CTX M] (ev : CoAnticipatedEvent v M α β) : AnticipatedEvent v M β α := ev

@[simp]
def CoAnticipatedEvent_from_AnticipatedEvent [Preorder v] [Machine CTX M] (ev : AnticipatedEvent v M α β) : CoAnticipatedEvent v M β α := ev

instance [Preorder v] [Machine CTX M]: Contravariant (CoAnticipatedEvent v M γ) where
  contramap {α β} (f : β → α) (ev : CoAnticipatedEvent v M γ α) :=
  let event := let ev' := coEvent_from_Event ev.to_Event
             let ev'' := Contravariant.contramap f ev'
             Event_from_CoEvent ev''
  {
    guard := event.guard
    action := event.action
    po := {
      safety := fun m x => by simp [Contravariant.contramap]
                              intros Hinv Hgrd
                              exact ev.po.safety m (f x) Hinv Hgrd
      variant := ev.po.variant
      nonIncreasing := fun m x => by simp
                                     intros Hinv Hgrd
                                     apply ev.po.nonIncreasing <;> assumption
    }
  }

instance [Preorder v] [Machine CTX M] : LawfullContravariant (CoAnticipatedEvent v M α) where
  cmap_id _ := by rfl
  cmap_comp _ _ := by rfl

abbrev CoConvergentEvent (v) [Preorder v] [WellFoundedLT v] (M) [Machine CTX M] (α) (β) :=
   ConvergentEvent v M β α

@[simp]
def ConvergentEvent_from_CoConvergentEvent [Preorder v] [WellFoundedLT v] [Machine CTX M] (ev : CoConvergentEvent v M α β) : ConvergentEvent v M β α := ev

@[simp]
def CoConvergentEvent_from_ConvergentEvent [Preorder v] [WellFoundedLT v] [Machine CTX M] (ev : ConvergentEvent v M α β) : CoConvergentEvent v M β α := ev

instance [Preorder v] [WellFoundedLT v] [Machine CTX M]: Contravariant (CoConvergentEvent v M γ) where
  contramap {α β} (f : β → α) (ev : CoConvergentEvent v M γ α) :=
  let event := let ev' := coEvent_from_Event ev.to_Event
             let ev'' := Contravariant.contramap f ev'
             Event_from_CoEvent ev''
  {
    guard := event.guard
    action := event.action
    po := {
      safety := fun m x => by simp [Contravariant.contramap]
                              intros Hinv Hgrd
                              exact ev.po.safety m (f x) Hinv Hgrd
      variant := ev.po.variant
      nonIncreasing := fun m x => by simp
                                     intros Hinv Hgrd
                                     apply ev.po.nonIncreasing <;> assumption
      convergence := fun m x => by simp
                                   intros Hinv Hgrd
                                   apply ev.po.convergence <;> assumption
    }
  }

instance [Preorder v] [WellFoundedLT v] [Machine CTX M] : LawfullContravariant (CoConvergentEvent v M α) where
  cmap_id _ := by rfl
  cmap_comp _ _ := by rfl

/- Profunctor -/

instance [Preorder v] [Machine CTX M] : Profunctor (AnticipatedEvent v M) where
  dimap {α β} {γ δ} (f : β → α) (g : γ → δ) (ev : AnticipatedEvent v M α γ) : AnticipatedEvent v M β δ :=
    let event := Profunctor.dimap f g ev.to_Event
    {
      guard := fun m x => ev.guard m (f x)
      action := fun m x => event.action m x
      po := {
        safety := fun m x => by simp [Profunctor.dimap]
                                intros Hinv Hgrd
                                let ev' := AnticipatedEvent_from_CoAnticipatedEvent (Contravariant.contramap f (CoAnticipatedEvent_from_AnticipatedEvent ev))
                                let ev'' := g <$> ev'
                                have Hsafe := ev''.po.safety m x Hinv
                                revert Hsafe ev' ev'' ; simp
                                intro Hsafe
                                exact Hsafe Hgrd

        variant := ev.po.variant

        nonIncreasing := fun m x => by simp
                                       intros Hinv Hgrd
                                       let ev' := AnticipatedEvent_from_CoAnticipatedEvent (Contravariant.contramap f (CoAnticipatedEvent_from_AnticipatedEvent ev))
                                       let ev'' := g <$> ev'
                                       have Hni := ev''.po.nonIncreasing m x Hinv
                                       revert Hni ev' ev'' ; simp [Functor.map, Contravariant.contramap]
                                       intro Hni
                                       apply Hni ; exact Hgrd
      }
    }

instance [Preorder v] [Machine CTX M] : LawfulProfunctor (AnticipatedEvent v M) where
  dimap_id := rfl
  dimap_comp _ _ _ _ := rfl

instance [Preorder v] [Machine CTX M] : StrongProfunctor (AnticipatedEvent v M) where
  first' {α β γ} (ev : AnticipatedEvent v M α β): AnticipatedEvent v M (α × γ) (β × γ) :=
    let event := StrongProfunctor.first' ev.to_Event
    {
      guard := fun m (x, y) => ev.guard m x ∧ event.guard m (x, y)
      action := event.action
      po := {
        safety := fun m x => by simp
                                intros Hinv _
                                apply ev.po.safety ; assumption

        variant := ev.po.variant

        nonIncreasing := fun m (x,y) => by simp
                                           intro Hinv _
                                           apply ev.po.nonIncreasing m x Hinv
      }
    }

instance [Preorder v] [Machine CTX M] : LawfulStrongProfunctor (AnticipatedEvent v M) where
  -- XXX : at some point the laws should be demonstrated

instance [Preorder v] [WellFoundedLT v] [Machine CTX M] : Profunctor (ConvergentEvent v M) where
  dimap {α β} {γ δ} (f : β → α) (g : γ → δ) (ev : ConvergentEvent v M α γ) : ConvergentEvent v M β δ :=
    let event := Profunctor.dimap f g ev.to_Event
    {
      guard := fun m x => ev.guard m (f x)
      action := fun m x => event.action m x
      po := {
        safety := fun m x => by simp [Profunctor.dimap]
                                intros Hinv Hgrd
                                let ev' := ConvergentEvent_from_CoConvergentEvent (Contravariant.contramap f (CoConvergentEvent_from_ConvergentEvent ev))
                                let ev'' := g <$> ev'
                                have Hsafe := ev''.po.safety m x Hinv
                                revert Hsafe ev' ev'' ; simp
                                intro Hsafe
                                exact Hsafe Hgrd

        variant := ev.po.variant

        nonIncreasing := fun m x => by simp
                                       intros Hinv Hgrd
                                       let ev' := ConvergentEvent_from_CoConvergentEvent (Contravariant.contramap f (CoConvergentEvent_from_ConvergentEvent ev))
                                       let ev'' := g <$> ev'
                                       have Hni := ev''.po.nonIncreasing m x Hinv
                                       revert Hni ev' ev'' ; simp [Functor.map, Contravariant.contramap]
                                       intro Hni
                                       apply Hni ; exact Hgrd

        convergence := fun m x => by simp
                                     intros Hinv Hgrd
                                     let ev' := ConvergentEvent_from_CoConvergentEvent (Contravariant.contramap f (CoConvergentEvent_from_ConvergentEvent ev))
                                     let ev'' := g <$> ev'
                                     have Hni := ev''.po.convergence m x Hinv
                                     revert Hni ev' ev'' ; simp [Functor.map, Contravariant.contramap]
                                     intro Hni
                                     apply Hni ; exact Hgrd
      }
    }

instance [Preorder v] [WellFoundedLT v] [Machine CTX M] : LawfulProfunctor (ConvergentEvent v M) where
  dimap_id := rfl
  dimap_comp _ _ _ _ := rfl

instance [Preorder v] [WellFoundedLT v] [Machine CTX M] : StrongProfunctor (ConvergentEvent v M) where
  first' {α β γ} (ev : ConvergentEvent v M α β): ConvergentEvent v M (α × γ) (β × γ) :=
    let event := StrongProfunctor.first' ev.to_Event
    {
      guard := fun m (x, y) => ev.guard m x ∧ event.guard m (x, y)
      action := event.action
      po := {
        safety := fun m x => by simp
                                intros Hinv _
                                apply ev.po.safety ; assumption

        variant := ev.po.variant

        nonIncreasing := fun m (x,y) => by simp
                                           intro Hinv _
                                           apply ev.po.nonIncreasing m x Hinv
        convergence := fun m (x,y) => by simp
                                         intro Hinv _
                                         apply ev.po.convergence m x Hinv

      }
    }

instance [Preorder v] [WellFoundedLT v] [Machine CTX M] : LawfulStrongProfunctor (ConvergentEvent v M) where
  -- XXX : at some point the laws should be demonstrated

/-

There are no Category or Arrow instances
 - for example, Category.id  has no nonIncreasing argument
   ==> or use a default zero ?
 - Category.comp is maybe possible (but non-trivial combination of variants)

==> probably needs more specific type classes to fix the precise constraints

-/
