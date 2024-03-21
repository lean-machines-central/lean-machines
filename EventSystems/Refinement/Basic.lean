
import EventSystems.Basic
import EventSystems.Convergent

class Refinement {ACTX : outParam (Type u₁)} (AM)
                    {CTX : outParam (Type u₂)} (M)
                    [Machine ACTX AM] [Machine CTX M] where

  refine : AM → M → Prop

  refine_inv (m : M) (am : AM):
    Machine.invariant m
    → refine am m
    → Machine.invariant am

open Refinement

structure _REvent (AM) [Machine ACTX AM]
                  (M) [Machine CTX M]
                  [Refinement AM M] (α) (β)
  extends _Event M α β where

  abstract : _Event AM α β

/- Functor -/

instance [Machine ACTX AM] [Machine CTX M] [Refinement AM M]: Functor (_REvent AM M γ) where
  map f ev := { to_Event := f <$> ev.to_Event
                abstract := f <$> ev.abstract }

instance [Machine ACTX AM] [Machine CTX M] [Refinement AM M]: LawfulFunctor (_REvent AM M γ) where
  map_const := by intros α β
                  simp [Functor.mapConst, Functor.map]
  id_map := by intros α ev
               simp [Functor.map, map_Event]
  comp_map := by intros α _ γ g h x
                 simp [Functor.map, map_Event]

/- arrows -/

instance [Machine ACTX AM] [Machine CTX M] [Refinement AM M]: Category (_REvent AM M) where
  id := {
    to_Event := Category.id
    abstract := Category.id
  }

  comp ev₂ ev₁ := {
      to_Event := Category.comp ev₂.to_Event ev₁.to_Event
      abstract := Category.comp ev₂.abstract ev₁.abstract
  }

instance [Machine CTX M]: LawfulCategory (_Event M) where
  id_right _ := by simp
  id_left _ := by simp
  id_assoc _ _ _ := by simp ; funext m x ; apply And_eq_assoc

instance  [Machine ACTX AM] [Machine CTX M] [Refinement AM M]:
          Arrow (_REvent AM M) where
  arrow f := {
    to_Event := Arrow.arrow f
    abstract := Arrow.arrow f
  }

  split ev₁ ev₂ := {
    to_Event := Arrow.split ev₁.to_Event ev₂.to_Event
    abstract := Arrow.split ev₁.abstract ev₂.abstract
  }

instance [Machine CTX M]: LawfulArrow (_Event M) where
  arrow_id := by simp [Arrow.arrow]
  arrow_ext _ := by simp [Arrow.arrow, Arrow.first]
  arrow_fun _ _ := by simp [Arrow.arrow, Arrow.first]
  arrow_xcg _ _ := by simp [Arrow.arrow, Arrow.first]
  arrow_unit _ := by simp [Arrow.arrow, Arrow.first]
  arrow_assoc {α β γ δ} (f : _Event M α β) :=
    by simp [Arrow.arrow, Arrow.first]

/- Contravariant functor -/

abbrev _CoREvent (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M] (α) (β) :=
  _REvent AM M β α

instance [Machine ACTX AM] [Machine CTX M] [Refinement AM M] : Contravariant (_CoREvent AM M γ) where
  contramap f ev :=
    let _coev : _CoEvent M γ _ := ev.to_Event
    let _abs : _CoEvent AM γ _ := ev.abstract
    {
      to_Event := Event_from_CoEvent (Contravariant.contramap f _coev)
      abstract := Event_from_CoEvent (Contravariant.contramap f ev.abstract)
    }

instance [Machine CTX M] : LawfullContravariant (_CoEvent M β) where
  cmap_id _ := rfl
  cmap_comp _ _ := rfl

/- Profunctor -/

instance [Machine ACTX AM] [Machine CTX M] [Refinement AM M] : Profunctor (_REvent AM M) where
  dimap f g ev := {
      to_Event := Profunctor.dimap f g ev.to_Event
      abstract := Profunctor.dimap f g ev.abstract
    }

instance [Machine ACTX AM] [Machine CTX M] [Refinement AM M] : LawfulProfunctor (_REvent AM M) where
  dimap_id := rfl
  dimap_comp _ _ _ _ := rfl

instance [Machine ACTX AM] [Machine CTX M] [Refinement AM M] : StrongProfunctor (_REvent AM M) where
  first' ev := {
      to_Event := StrongProfunctor.first' ev.to_Event
      abstract := StrongProfunctor.first' ev.abstract
    }

instance [Machine ACTX AM] [Machine CTX M] [Refinement AM M] : LawfulStrongProfunctor (_REvent AM M) where


structure _REventPO  [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
   (ev : _Event M α β) (kind : EventKind)
   extends _EventPO ev kind where

  abstract : _Event AM α β

  strengthening (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → ∀ am, refine am m
      → abstract.guard am x

  simulation (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → ∀ am, refine am m
      -- XXX : some constraint on output ?
      --       (maybe a post_weakening requirement ?)
      --       for now, let's go with equality because its transparent for the Event-B
      --       refinement model
      → let (y, m') := ev.action m x
        let (z, am') := abstract.action am x
        y = z ∧ refine am' m'


structure OrdinaryREvent (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M] (α) (β) extends _Event M α β where
  po : _REventPO (instR:=instR) to_Event (EventKind.TransDet Convergence.Ordinary)
