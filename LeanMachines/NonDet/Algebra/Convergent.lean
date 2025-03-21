
import LeanMachines.NonDet.Algebra.Ordinary
import LeanMachines.NonDet.Convergent

/-!
## Algebraic properties

The following instantiate various algebraic structures for anticipated
and convergent non-deterministic events (experimental, not documented).

-/

instance [Preorder v] [Machine CTX M] : Functor (AnticipatedNDEvent v M γ) where
  map f ev := {
    toNDEvent := f <$> ev.toNDEvent
    safety := fun m x => by
        simp [Functor.map]
        intros Hinv Hgrd _ m' x' Heff _
        apply ev.safety m x Hinv Hgrd x' m' Heff

    feasibility := fun m x => by
        simp [Functor.map]
        intros Hinv Hgrd
        have Hfeas := ev.feasibility m x Hinv Hgrd
        obtain ⟨y, m', Heff⟩ := Hfeas
        exists (f y) ; exists m' ; exists y

    variant := ev.variant

    nonIncreasing := fun m x => by
        simp [Functor.map]
        intros Hinv Hgrd _ m' x' Heff _
        have Hni := ev.nonIncreasing m x Hinv Hgrd x' m'
        apply Hni ; assumption

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
    toNDEvent := f <$> ev.toNDEvent
    safety := fun m x => by
        simp [Functor.map]
        intros Hinv Hgrd _ m' x' Heff _
        apply ev.safety m x Hinv Hgrd x' m' Heff

    feasibility := fun m x => by
        simp [Functor.map]
        intros Hinv Hgrd
        have Hfeas := ev.feasibility m x Hinv Hgrd
        obtain ⟨y, m', Heff⟩ := Hfeas
        exists (f y) ; exists m' ; exists y

    variant := ev.variant

    convergence := fun m x => by
        simp [Functor.map]
        intros Hinv Hgrd _ m' x' Heff _
        have Hcv := ev.convergence m x Hinv Hgrd x' m'
        apply Hcv ; assumption

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
  let ev : CoNDEvent M γ β := ContravariantFunctor.contramap f event.toNDEvent
  {
     toNDEvent := ev
     safety := fun m x Hinv Hgrd y m' Heff =>
        event.safety m (f x) Hinv Hgrd y m' Heff

     feasibility := fun m x Hinv Hgrd => by
       exact event.feasibility m (f x) Hinv Hgrd

     variant := event.variant

     nonIncreasing := fun m x Hinv Hgrd y m' Heff =>
       by exact event.nonIncreasing m (f x) Hinv Hgrd y m' Heff
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
  let ev : CoNDEvent M γ β := ContravariantFunctor.contramap f event.toNDEvent
  {
     toNDEvent := ev
     safety := fun m x Hinv Hgrd y m' Heff =>
        event.safety m (f x) Hinv Hgrd y m' Heff

     feasibility := fun m x Hinv Hgrd => by
       exact event.feasibility m (f x) Hinv Hgrd

     variant := event.variant

     convergence := fun m x Hinv Hgrd y m' Heff =>
       by exact event.convergence m (f x) Hinv Hgrd y m' Heff
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
    let ev : NDEvent M (α × γ) (β × γ) := StrongProfunctor.first' event.toNDEvent
    {
      guard := ev.guard
      effect := ev.effect
      safety := fun m (x, z) => by
          simp [ev, StrongProfunctor.first']
          intros Hinv Hgrd
          have Hsafe := event.safety m x Hinv Hgrd
          intros y _ m' _ Heff
          apply Hsafe y m' Heff

      feasibility := fun m (x, z) => by
          simp [ev, StrongProfunctor.first']
          intro Hinv Hgrd
          have Hfeas := event.feasibility m x Hinv Hgrd
          obtain ⟨y, m', Hfeas⟩ := Hfeas
          exists y
          exists m'

      variant := event.variant

      nonIncreasing := fun m (x, z) => by
          simp [ev, StrongProfunctor.first']
          intros Hinv Hgrd
          intros y _ m' _ Heff
          have Hni := event.nonIncreasing m x Hinv Hgrd y m'
          apply Hni
          assumption

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
    let ev : NDEvent M (α × γ) (β × γ) := StrongProfunctor.first' event.toNDEvent
    {
      guard := ev.guard
      effect := ev.effect
      safety := fun m (x, z) => by
          simp [ev, StrongProfunctor.first']
          intros Hinv Hgrd
          have Hsafe := event.safety m x Hinv Hgrd
          intros y _ m' _ Heff
          apply Hsafe y m' Heff

      feasibility := fun m (x, z) => by
          simp [ev, StrongProfunctor.first']
          intro Hinv Hgrd
          have Hfeas := event.feasibility m x Hinv Hgrd
          obtain ⟨y, m', Hfeas⟩ := Hfeas
          exists y
          exists m'

      variant := event.variant

      convergence := fun m (x, z) => by
          simp [ev, StrongProfunctor.first']
          intros Hinv Hgrd
          intros y _ m' _ Heff
          have Hcv := event.convergence m x Hinv Hgrd y m'
          apply Hcv
          assumption

      }


-- TODO: lawful strong profunctor
-- instance [Preorder v] [WellFoundedLT v] [Machine CTX M] : LawfulStrongProfunctor (ConvergentNDEvent v M) where
