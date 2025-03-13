import LeanMachines.Event.Prelude
import LeanMachines.Event.Basic
import LeanMachines.Algebra.Contravariant
import LeanMachines.Algebra.Profunctor
import LeanMachines.Algebra.Arrow
import LeanMachines.Event.Ordinary
import LeanMachines.Event.Convergent

import LeanMachines.Event.Algebra.Ordinary
import LeanMachines.Event.Algebra.Basic








/-!
## Algebraic properties of events

The following instantiate various algebraic structures for anticipated
and convergent events (experimental, not documented).

-/

@[simp]
def mapAnticipatedEvent [Preorder v] [Machine CTX M] (f : α → β) (ev : _AnticipatedEvent v M γ α) : _AnticipatedEvent v M γ β :=
  {
    guard := ev.guard
    action := fun m x grd => let (y, m') := ev.action m x grd
                             (f y, m')
    safety :=  ev.safety
    variant := ev.variant
    nonIncreasing := ev.nonIncreasing
  }

instance [Preorder v] [Machine CTX M] : Functor (_AnticipatedEvent v M γ) where
  map := mapAnticipatedEvent

instance [Preorder v] [Machine CTX M] : LawfulFunctor (_AnticipatedEvent v M γ) where
  map_const := rfl
  id_map := by intros ; rfl
  comp_map := by intros ; rfl

def mapConvergentEvent [Preorder v] [WellFoundedLT v] [Machine CTX M] (f : α → β) (ev : _ConvergentEvent v M γ α) : _ConvergentEvent v M γ β :=
  {
    guard := ev.guard
    action := fun m x grd => let (y, m') := ev.action m x grd
                             (f y, m')
    safety :=  ev.safety
    variant := ev.variant
    convergence := ev.convergence
  }

instance [Preorder v] [WellFoundedLT v] [Machine CTX M] : Functor (_ConvergentEvent v M γ) where
  map := mapConvergentEvent

instance [Preorder v] [WellFoundedLT v] [Machine CTX M] : LawfulFunctor (_ConvergentEvent v M γ) where
  map_const := rfl
  id_map := by intros ; rfl
  comp_map := by intros ; rfl

/- Contravariant functor -/

abbrev CoAnticipatedEvent (v) [Preorder v] (M) [Machine CTX M] (α) (β) :=
   _AnticipatedEvent v M β α

@[simp]
def AnticipatedEvent_from_CoAnticipatedEvent [Preorder v] [Machine CTX M] (ev : CoAnticipatedEvent v M α β) : _AnticipatedEvent v M β α := ev

@[simp]
def CoAnticipatedEvent_from_AnticipatedEvent [Preorder v] [Machine CTX M] (ev : _AnticipatedEvent v M α β) : CoAnticipatedEvent v M β α := ev

instance [Preorder v] [Machine CTX M]: ContravariantFunctor (CoAnticipatedEvent v M γ) where
  contramap {α β} (f : β → α) (ev : CoAnticipatedEvent v M γ α) :=
  let event := let ev' := coEvent_from_Event ev.toEvent
             let ev'' := ContravariantFunctor.contramap f ev'
             Event_from_CoEvent ev''
  {
    guard := event.guard
    action := event.action
    safety := fun m x => by
      intros Hinv Hgrd
      exact ev.safety m (f x) Hinv Hgrd
    variant := ev.variant
    nonIncreasing := fun m x => by
      simp
      intros Hinv Hgrd
      apply ev.nonIncreasing
      assumption

  }

instance [Preorder v] [Machine CTX M] : LawfullContravariantFunctor (CoAnticipatedEvent v M α) where
  cmap_id _ := by rfl
  cmap_comp _ _ := by rfl

abbrev CoConvergentEvent (v) [Preorder v] [WellFoundedLT v] (M) [Machine CTX M] (α) (β) :=
   _ConvergentEvent v M β α

@[simp]
def ConvergentEvent_from_CoConvergentEvent [Preorder v] [WellFoundedLT v] [Machine CTX M] (ev : CoConvergentEvent v M α β) : _ConvergentEvent v M β α := ev

@[simp]
def CoConvergentEvent_from_ConvergentEvent [Preorder v] [WellFoundedLT v] [Machine CTX M] (ev : _ConvergentEvent v M α β) : CoConvergentEvent v M β α := ev

instance [Preorder v] [WellFoundedLT v] [Machine CTX M]: ContravariantFunctor (CoConvergentEvent v M γ) where
  contramap {α β} (f : β → α) (ev : CoConvergentEvent v M γ α) :=
  let event := let ev' := coEvent_from_Event ev.toEvent
             let ev'' := ContravariantFunctor.contramap f ev'
             Event_from_CoEvent ev''
  {
    guard := event.guard
    action := event.action
    safety := fun m x =>
      by
        intros Hinv Hgrd
        exact ev.safety m (f x) Hinv Hgrd
    variant := ev.variant
    -- nonIncreasing := fun m x => by simp
    --                                intros Hinv Hgrd
    --                                apply ev.nonIncreasing ; assumption
    convergence := fun m x => by simp
                                 intros Hinv Hgrd
                                 apply ev.convergence ; assumption

  }

instance [Preorder v] [WellFoundedLT v] [Machine CTX M] : LawfullContravariantFunctor (CoConvergentEvent v M α) where
  cmap_id _ := by rfl
  cmap_comp _ _ := by rfl

/- Profunctor -/

instance [Preorder v] [Machine CTX M] : Profunctor (_AnticipatedEvent v M) where
  dimap {α β} {γ δ} (f : β → α) (g : γ → δ) (ev : _AnticipatedEvent v M α γ) : _AnticipatedEvent v M β δ :=
    let event := Profunctor.dimap f g ev.toEvent
    {
      guard := fun m x => ev.guard m (f x)
      action := fun m x => event.action m x

      safety := fun m x => by
        simp [Profunctor.dimap]
        intros Hinv Hgrd
        let ev' := AnticipatedEvent_from_CoAnticipatedEvent (ContravariantFunctor.contramap f (CoAnticipatedEvent_from_AnticipatedEvent ev))
        let ev'' := g <$> ev'
        have Hsafe := ev''.safety m x Hinv
        revert Hsafe ev' ev'' ; simp
        intro Hsafe
        exact Hsafe Hgrd
      variant := ev.variant
      nonIncreasing := fun m x => by
        simp
        intros Hinv Hgrd
        let ev' := AnticipatedEvent_from_CoAnticipatedEvent (ContravariantFunctor.contramap f (CoAnticipatedEvent_from_AnticipatedEvent ev))
        let ev'' := g <$> ev'
        have Hni := ev''.nonIncreasing m x Hinv
        revert Hni ev' ev'' ; simp [Functor.map, ContravariantFunctor.contramap]
        intro Hni
        apply Hni

    }

instance [Preorder v] [Machine CTX M] : LawfulProfunctor (_AnticipatedEvent v M) where
  dimap_id := rfl
  dimap_comp _ _ _ _ := rfl

instance [Preorder v] [Machine CTX M] : StrongProfunctor (_AnticipatedEvent v M) where
  first' {α β γ} (ev : _AnticipatedEvent v M α β): _AnticipatedEvent v M (α × γ) (β × γ) :=
    let event := StrongProfunctor.first' ev.toEvent
    {
      guard := fun m (x, y) => ev.guard m x ∧ event.guard m (x, y)
      action := fun m (x, y) grd => event.action m (x, y) grd.2

      safety := fun m x => by simp
                              intros Hinv _
                              apply ev.safety ; assumption
      variant := ev.variant
      nonIncreasing := fun m (x,y) => by
        simp
        intro Hinv _
        apply ev.nonIncreasing m x Hinv

    }

instance [Preorder v] [Machine CTX M] : LawfulStrongProfunctor (_AnticipatedEvent v M) where
  -- XXX : at some point the laws should be demonstrated

instance [Preorder v] [WellFoundedLT v] [Machine CTX M] : Profunctor (_ConvergentEvent v M) where
  dimap {α β} {γ δ} (f : β → α) (g : γ → δ) (ev : _ConvergentEvent v M α γ) : _ConvergentEvent v M β δ :=
    let event := Profunctor.dimap f g ev.toEvent
    {
      guard := fun m x => ev.guard m (f x)
      action := fun m x => event.action m x
      safety := fun m x => by
        simp [Profunctor.dimap]
        intros Hinv Hgrd
        let ev' := ConvergentEvent_from_CoConvergentEvent (ContravariantFunctor.contramap f (CoConvergentEvent_from_ConvergentEvent ev))
        let ev'' := g <$> ev'
        have Hsafe := ev''.safety m x Hinv
        revert Hsafe ev' ev'' ; simp
        intro Hsafe
        exact Hsafe Hgrd
      variant := ev.variant

      convergence := fun m x => by
        simp
        intros Hinv Hgrd
        let ev' := ConvergentEvent_from_CoConvergentEvent (ContravariantFunctor.contramap f (CoConvergentEvent_from_ConvergentEvent ev))
        let ev'' := g <$> ev'
        have Hni := ev''.convergence m x Hinv
        revert Hni ev' ev'' ; simp [Functor.map, ContravariantFunctor.contramap]
        intro Hni
        apply Hni
    }

instance [Preorder v] [WellFoundedLT v] [Machine CTX M] : LawfulProfunctor (_ConvergentEvent v M) where
  dimap_id := rfl
  dimap_comp _ _ _ _ := rfl

instance [Preorder v] [WellFoundedLT v] [Machine CTX M] : StrongProfunctor (_ConvergentEvent v M) where
  first' {α β γ} (ev : _ConvergentEvent v M α β): _ConvergentEvent v M (α × γ) (β × γ) :=
    let event := StrongProfunctor.first' ev.toEvent
    {
      guard := fun m (x, y) => ev.guard m x ∧ event.guard m (x, y)
      action := fun m (x, y) grd => event.action m (x, y) grd.2
      safety := fun m x => by
        simp
        intros Hinv _
        apply ev.safety ; assumption
      variant := ev.variant

      convergence := fun m (x,y) => by
        simp
        intro Hinv _
        apply ev.convergence m x Hinv
    }

instance [Preorder v] [WellFoundedLT v] [Machine CTX M] : LawfulStrongProfunctor (_ConvergentEvent v M) where
  -- XXX : at some point the laws should be demonstrated

/-

There are no Category or Arrow instances
 - for example, Category.id  has no nonIncreasing argument
   ==> or use a default zero ?
 - Category.comp is maybe possible (but non-trivial combination of variants)

==> probably needs more specific type classes to fix the precise constraints

-/
