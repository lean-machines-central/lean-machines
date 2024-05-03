
import EventSystems.NonDet.Ordinary
import EventSystems.Refinement.Relational.NonDet.Basic
import EventSystems.Refinement.Relational.NonDet.Convergent
import EventSystems.Refinement.Relational.Abstract

open Refinement

structure _AbstractRNDEventSpec (AM) [Machine ACTX AM]
                               (M) [Machine CTX M]
                               [Refinement AM M] (α) (β) (event : _NDEvent AM α β)
          extends _AbstractREventSpec AM M α where



structure AbstractRNDEventSpec (AM) [Machine ACTX AM]
                               (M) [Machine CTX M]
                               [Refinement AM M] (α) (β)
          extends _AbstractREventSpec AM M α where

  event : OrdinaryNDEvent AM α β

  step_ref (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → ∀ y, ∀ am', event.effect (lift m) x (y, am')
                  → refine am' (unlift (lift m) am' m x)

  step_safe (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → ∀ y, ∀ am', event.effect (lift m) x (y, am')
                  → Machine.invariant (unlift (lift m) am' m x)

  /- Note : was required before strengthening the effect
  step_conc (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → ∀ y, ∀ m', event.effect (lift m) x (y, lift m')
                  → Machine.invariant (lift m')
                  → Machine.invariant m'
  -/

  lift_unlift (m : M) (am am' : AM) (x : α):
    Machine.invariant m → Machine.invariant am'
    → lift (unlift am am' m x) = am'


@[simp]
def newAbstractRNDEvent [Machine ACTX AM] [Machine CTX M] [instR:Refinement AM M]
  (abs : AbstractRNDEventSpec AM M α β) : OrdinaryRNDEvent AM M α β :=
  {
    guard := fun m x => abs.event.guard (abs.lift m) x
    effect := fun m x (y, m') => abs.event.effect (abs.lift m) x (y, abs.lift m')
                                 ∧ m' = abs.unlift (abs.lift m) (abs.lift m') m x
    po := {
      safety := fun m x => by
        simp
        intros Hinv Hagrd y m' Heff Hm'
        --have Href := abs.lift_ref m Hinv
        --have Hainv := refine_safe (abs.lift m) m Hinv Href
        --have Hainv' := abs.event.po.safety (abs.lift m) x Hainv Hagrd y (abs.lift m') Heff
        rw [Hm']
        apply abs.step_safe m x Hinv Hagrd y (abs.lift m') Heff

      feasibility := fun m x => by
        simp
        intros Hinv Hagrd
        have Href := abs.lift_ref m Hinv
        have Hainv := refine_safe (abs.lift m) m Hinv Href
        obtain ⟨y, am', Hafeas⟩ := abs.event.po.feasibility (abs.lift m) x Hainv Hagrd
        exists y
        exists (abs.unlift (abs.lift m) am' m x)
        have Hsref := abs.step_ref m x Hinv Hagrd y am' Hafeas
        have Hssafe := abs.step_safe m x Hinv Hagrd y am' Hafeas
        have Hasafe' := refine_safe am' (abs.unlift (abs.lift m) am' m x) Hssafe Hsref
        have Hlu := abs.lift_unlift m (abs.lift m) am' x Hinv Hasafe'
        rw [Hlu]
        simp [Hafeas]

      abstract := abs.event.to_NDEvent

      strengthening := fun m x => by
        simp
        intros Hinv Hagrd am Href
        have Href' := abs.lift_ref m Hinv
        have Huniq := abs.refine_uniq am (abs.lift m) m Hinv Href Href'
        rw [Huniq]
        exact Hagrd

      simulation := fun m x => by
        simp
        intros Hinv Hagrd y m' Heff Hm' am Href
        have Href' := abs.lift_ref m Hinv
        exists (abs.lift m')
        constructor
        · have Huniq := abs.refine_uniq am (abs.lift m) m Hinv Href Href'
          rw [Huniq]
          exact Heff
        -- and
        rw [Hm']
        rw [abs.lift_unlift]
        · apply abs.step_ref m x Hinv Hagrd y (abs.lift m') Heff
        · assumption
        -- finally
        have Hainv := refine_safe (abs.lift m) m Hinv Href'
        apply abs.event.po.safety (abs.lift m) x Hainv Hagrd y (abs.lift m') Heff
    }
  }

structure AbstractRNDEventSpec' (AM) [Machine ACTX AM]
                               (M) [Machine CTX M]
                               [Refinement AM M] (α)
          extends _AbstractREventSpec AM M α where

  event : OrdinaryNDEvent AM α Unit

  step_ref (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → ∀ am', event.effect (lift m) x ((), am')
             → refine am' (unlift (lift m) am' m x)

  step_safe (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → ∀ am', event.effect (lift m) x ((), am')
            → Machine.invariant (unlift (lift m) am' m x)

  lift_unlift (m : M) (am am' : AM) (x : α):
    Machine.invariant m → Machine.invariant am'
    → lift (unlift am am' m x) = am'

@[simp]
def AbstractRNDEventSpec'.toAbstractRNDEventSpec  [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : AbstractRNDEventSpec' AM M α) : AbstractRNDEventSpec AM M α Unit :=
  {
    to_AbstractREventSpec := ev.to_AbstractREventSpec
    event := ev.event
    step_ref := fun m x Hinv Hgrd _ am' => ev.step_ref m x Hinv Hgrd am'
    step_safe := fun m x Hinv Hgrd _ am' => ev.step_safe m x Hinv Hgrd am'
    lift_unlift := ev.lift_unlift
  }

@[simp]
def newAbstractRNDEvent' [Machine ACTX AM] [Machine CTX M] [instR:Refinement AM M]
  (ev : AbstractRNDEventSpec' AM M α) : OrdinaryRNDEvent AM M α Unit :=
  newAbstractRNDEvent ev.toAbstractRNDEventSpec

structure AbstractRNDEventSpec'' (AM) [Machine ACTX AM]
                               (M) [Machine CTX M]
                               [Refinement AM M]
          extends _AbstractREventSpec AM M Unit where

  event : OrdinaryNDEvent AM Unit Unit

  step_ref (m : M):
    Machine.invariant m
    → event.guard (lift m) ()
    → ∀ am', event.effect (lift m) () ((), am')
             → refine am' (unlift (lift m) am' m ())

  step_safe (m : M):
    Machine.invariant m
    → event.guard (lift m) ()
    → ∀ am', event.effect (lift m) () ((), am')
            → Machine.invariant (unlift (lift m) am' m ())

  lift_unlift (m : M) (am am' : AM):
    Machine.invariant m → Machine.invariant am'
    → lift (unlift am am' m ()) = am'

@[simp]
def AbstractRNDEventSpec''.toAbstractRNDEventSpec  [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : AbstractRNDEventSpec'' AM M) : AbstractRNDEventSpec AM M Unit Unit :=
  {
    to_AbstractREventSpec := ev.to_AbstractREventSpec
    event := ev.event
    step_ref := fun m _ Hinv Hgrd _ am' => ev.step_ref m Hinv Hgrd am'
    step_safe := fun m _ Hinv Hgrd _ am' => ev.step_safe m Hinv Hgrd am'
    lift_unlift := fun m am am' _ => ev.lift_unlift m am am'
  }

@[simp]
def newAbstractRNDEvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : AbstractRNDEventSpec'' AM M) : OrdinaryRNDEvent AM M Unit Unit :=
  newAbstractRNDEvent ev.toAbstractRNDEventSpec

structure AbstractAnticipatedRNDEventSpec
              (v) [Preorder v]
              (AM) [Machine ACTX AM]
              (M) [Machine CTX M]
              [Refinement AM M] (α) (β)
          extends _AbstractREventSpec AM M α where

  event : AnticipatedNDEvent v AM α β

  step_ref (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → ∀ y, ∀ am', event.effect (lift m) x (y, am')
                  → refine am' (unlift (lift m) am' m x)

  step_safe (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → ∀ y, ∀ am', event.effect (lift m) x (y, am')
                  → Machine.invariant (unlift (lift m) am' m x)

  lift_unlift (m : M) (am am' : AM) (x : α):
    Machine.invariant m → Machine.invariant am'
    → lift (unlift am am' m x) = am'

  /- Note: this is not needed, unlike in the determinstic case
  step_variant (m : M) (x : α):
      Machine.invariant m
    → event.guard (lift m) x
    → ∀ y, ∀ am', event.effect (lift m) x (y, am')
                  → Machine.invariant am' -- redundant but useful
                  → event.po.variant (lift (unlift (lift m) am' m x))
                    = event.po.variant am' -/

@[simp]
def newAbstractAnticipatedRNDEvent [Preorder v] [Machine ACTX AM] [Machine CTX M] [instR:Refinement AM M]
  (abs : AbstractAnticipatedRNDEventSpec v AM M α β) : AnticipatedRNDEvent v AM M α β :=
  {
    guard := fun m x => abs.event.guard (abs.lift m) x
    effect := fun m x (y, m') => abs.event.effect (abs.lift m) x (y, abs.lift m')
                                 ∧ m' = abs.unlift (abs.lift m) (abs.lift m') m x
    po := {
      safety := fun m x => by
        simp
        intros Hinv Hagrd y m' Heff Hm'
        --have Href := abs.lift_ref m Hinv
        --have Hainv := refine_safe (abs.lift m) m Hinv Href
        --have Hainv' := abs.event.po.safety (abs.lift m) x Hainv Hagrd y (abs.lift m') Heff
        rw [Hm']
        apply abs.step_safe m x Hinv Hagrd y (abs.lift m') Heff

      feasibility := fun m x => by
        simp
        intros Hinv Hagrd
        have Href := abs.lift_ref m Hinv
        have Hainv := refine_safe (abs.lift m) m Hinv Href
        obtain ⟨y, am', Hafeas⟩ := abs.event.po.feasibility (abs.lift m) x Hainv Hagrd
        exists y
        exists (abs.unlift (abs.lift m) am' m x)
        have Hsref := abs.step_ref m x Hinv Hagrd y am' Hafeas
        have Hssafe := abs.step_safe m x Hinv Hagrd y am' Hafeas
        have Hasafe' := refine_safe am' (abs.unlift (abs.lift m) am' m x) Hssafe Hsref
        have Hlu := abs.lift_unlift m (abs.lift m) am' x Hinv Hasafe'
        rw [Hlu]
        simp [Hafeas]

      abstract := abs.event.to_NDEvent

      strengthening := fun m x => by
        simp
        intros Hinv Hagrd am Href
        have Href' := abs.lift_ref m Hinv
        have Huniq := abs.refine_uniq am (abs.lift m) m Hinv Href Href'
        rw [Huniq]
        exact Hagrd

      simulation := fun m x => by
        simp
        intros Hinv Hagrd y m' Heff Hm' am Href
        have Href' := abs.lift_ref m Hinv
        exists (abs.lift m')
        constructor
        · have Huniq := abs.refine_uniq am (abs.lift m) m Hinv Href Href'
          rw [Huniq]
          exact Heff
        -- and
        rw [Hm']
        rw [abs.lift_unlift]
        · apply abs.step_ref m x Hinv Hagrd y (abs.lift m') Heff
        · assumption
        -- finally
        have Hainv := refine_safe (abs.lift m) m Hinv Href'
        apply abs.event.po.safety (abs.lift m) x Hainv Hagrd y (abs.lift m') Heff

      variant := fun m => abs.event.po.variant (abs.lift m)

      nonIncreasing := fun m x => by
        simp
        intros Hinv Hgrd y m' Heff _
        have Hinv' := Refinement.refine_safe (abs.lift m) m Hinv (abs.lift_ref m Hinv)
        apply abs.event.po.nonIncreasing (abs.lift m) x Hinv' Hgrd y (abs.lift m') Heff

    }
  }

structure AbstractAnticipatedRNDEventSpec'
              (v) [Preorder v]
              (AM) [Machine ACTX AM]
              (M) [Machine CTX M]
              [Refinement AM M] (α)
          extends _AbstractREventSpec AM M α where

  event : AnticipatedNDEvent v AM α Unit

  step_ref (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → ∀ am', event.effect (lift m) x ((), am')
             → refine am' (unlift (lift m) am' m x)

  step_safe (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → ∀ am', event.effect (lift m) x ((), am')
             → Machine.invariant (unlift (lift m) am' m x)

  lift_unlift (m : M) (am am' : AM) (x : α):
    Machine.invariant m → Machine.invariant am'
    → lift (unlift am am' m x) = am'

@[simp]
def AbstractAnticipatedRNDEventSpec'.toAbstractAnticipatedRNDEventSpec  [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : AbstractAnticipatedRNDEventSpec' v AM M α) : AbstractAnticipatedRNDEventSpec v AM M α Unit :=
  {
    to_AbstractREventSpec := ev.to_AbstractREventSpec
    event := ev.event
    step_ref := fun m x Hinv Hgrd _ => ev.step_ref m x Hinv Hgrd
    step_safe := fun m x Hinv Hgrd _ => ev.step_safe m x Hinv Hgrd
    lift_unlift := ev.lift_unlift
  }

@[simp]
def newAbstractAnticipatedRNDEvent' [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : AbstractAnticipatedRNDEventSpec' v AM M α) : AnticipatedRNDEvent v AM M α Unit :=
  newAbstractAnticipatedRNDEvent abs.toAbstractAnticipatedRNDEventSpec

structure AbstractAnticipatedRNDEventSpec''
              (v) [Preorder v]
              (AM) [Machine ACTX AM]
              (M) [Machine CTX M]
              [Refinement AM M]
          extends _AbstractREventSpec AM M Unit where

  event : AnticipatedNDEvent v AM Unit Unit

  step_ref (m : M):
    Machine.invariant m
    → event.guard (lift m) ()
    → ∀ am', event.effect (lift m) () ((), am')
             → refine am' (unlift (lift m) am' m ())

  step_safe (m : M):
    Machine.invariant m
    → event.guard (lift m) ()
    → ∀ am', event.effect (lift m) () ((), am')
             → Machine.invariant (unlift (lift m) am' m ())

  lift_unlift (m : M) (am am' : AM):
    Machine.invariant m → Machine.invariant am'
    → lift (unlift am am' m ()) = am'

@[simp]
def AbstractAnticipatedRNDEventSpec''.toAbstractAnticipatedRNDEventSpec  [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : AbstractAnticipatedRNDEventSpec'' v AM M) : AbstractAnticipatedRNDEventSpec v AM M Unit Unit :=
  {
    to_AbstractREventSpec := ev.to_AbstractREventSpec
    event := ev.event
    step_ref := fun m _ Hinv Hgrd _ => ev.step_ref m Hinv Hgrd
    step_safe := fun m _ Hinv Hgrd _ => ev.step_safe m Hinv Hgrd
    lift_unlift := fun m am am' _ => ev.lift_unlift m am am'
  }

@[simp]
def newAbstractAnticipatedRNDEvent'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : AbstractAnticipatedRNDEventSpec'' v AM M) : AnticipatedRNDEvent v AM M Unit Unit :=
  newAbstractAnticipatedRNDEvent abs.toAbstractAnticipatedRNDEventSpec

structure AbstractConvergentRNDEventSpec
              (v) [Preorder v] [WellFoundedLT v]
              (AM) [Machine ACTX AM]
              (M) [Machine CTX M]
              [Refinement AM M] (α) (β)
          extends _AbstractREventSpec AM M α where

  event : ConvergentNDEvent v AM α β

  step_ref (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → ∀ y, ∀ am', event.effect (lift m) x (y, am')
                  → refine am' (unlift (lift m) am' m x)

  step_safe (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → ∀ y, ∀ am', event.effect (lift m) x (y, am')
                  → Machine.invariant (unlift (lift m) am' m x)

  lift_unlift (m : M) (am am' : AM) (x : α):
    Machine.invariant m → Machine.invariant am'
    → lift (unlift am am' m x) = am'

@[simp]
def newAbstractConvergentRNDEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instR:Refinement AM M]
  (abs : AbstractConvergentRNDEventSpec v AM M α β) : ConvergentRNDEvent v AM M α β :=
  {
    guard := fun m x => abs.event.guard (abs.lift m) x
    effect := fun m x (y, m') => abs.event.effect (abs.lift m) x (y, abs.lift m')
                                 ∧ m' = abs.unlift (abs.lift m) (abs.lift m') m x
    po := {
      safety := fun m x => by
        simp
        intros Hinv Hagrd y m' Heff Hm'
        --have Href := abs.lift_ref m Hinv
        --have Hainv := refine_safe (abs.lift m) m Hinv Href
        --have Hainv' := abs.event.po.safety (abs.lift m) x Hainv Hagrd y (abs.lift m') Heff
        rw [Hm']
        apply abs.step_safe m x Hinv Hagrd y (abs.lift m') Heff

      feasibility := fun m x => by
        simp
        intros Hinv Hagrd
        have Href := abs.lift_ref m Hinv
        have Hainv := refine_safe (abs.lift m) m Hinv Href
        obtain ⟨y, am', Hafeas⟩ := abs.event.po.feasibility (abs.lift m) x Hainv Hagrd
        exists y
        exists (abs.unlift (abs.lift m) am' m x)
        have Hsref := abs.step_ref m x Hinv Hagrd y am' Hafeas
        have Hssafe := abs.step_safe m x Hinv Hagrd y am' Hafeas
        have Hasafe' := refine_safe am' (abs.unlift (abs.lift m) am' m x) Hssafe Hsref
        have Hlu := abs.lift_unlift m (abs.lift m) am' x Hinv Hasafe'
        rw [Hlu]
        simp [Hafeas]

      abstract := abs.event.to_NDEvent

      strengthening := fun m x => by
        simp
        intros Hinv Hagrd am Href
        have Href' := abs.lift_ref m Hinv
        have Huniq := abs.refine_uniq am (abs.lift m) m Hinv Href Href'
        rw [Huniq]
        exact Hagrd

      simulation := fun m x => by
        simp
        intros Hinv Hagrd y m' Heff Hm' am Href
        have Href' := abs.lift_ref m Hinv
        exists (abs.lift m')
        constructor
        · have Huniq := abs.refine_uniq am (abs.lift m) m Hinv Href Href'
          rw [Huniq]
          exact Heff
        -- and
        rw [Hm']
        rw [abs.lift_unlift]
        · apply abs.step_ref m x Hinv Hagrd y (abs.lift m') Heff
        · assumption
        -- finally
        have Hainv := refine_safe (abs.lift m) m Hinv Href'
        apply abs.event.po.safety (abs.lift m) x Hainv Hagrd y (abs.lift m') Heff

      variant := fun m => abs.event.po.variant (abs.lift m)

      nonIncreasing := fun m x => by
        simp
        intros Hinv Hgrd y m' Heff _
        have Hinv' := Refinement.refine_safe (abs.lift m) m Hinv (abs.lift_ref m Hinv)
        apply abs.event.po.nonIncreasing (abs.lift m) x Hinv' Hgrd y (abs.lift m') Heff

      convergence := fun m x => by
        simp
        intros Hinv Hgrd y m' Heff _
        have Hinv' := Refinement.refine_safe (abs.lift m) m Hinv (abs.lift_ref m Hinv)
        apply abs.event.po.convergence (abs.lift m) x Hinv' Hgrd y (abs.lift m') Heff

    }
  }

structure AbstractConvergentRNDEventSpec'
              (v) [Preorder v] [WellFoundedLT v]
              (AM) [Machine ACTX AM]
              (M) [Machine CTX M]
              [Refinement AM M] (α)
          extends _AbstractREventSpec AM M α where

  event : ConvergentNDEvent v AM α Unit

  step_ref (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → ∀ am', event.effect (lift m) x ((), am')
             → refine am' (unlift (lift m) am' m x)

  step_safe (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → ∀ am', event.effect (lift m) x ((), am')
             → Machine.invariant (unlift (lift m) am' m x)

  lift_unlift (m : M) (am am' : AM) (x : α):
    Machine.invariant m → Machine.invariant am'
    → lift (unlift am am' m x) = am'


@[simp]
def AbstractConvergentRNDEventSpec'.toAbstractConvergentRNDEventSpec  [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : AbstractConvergentRNDEventSpec' v AM M α) : AbstractConvergentRNDEventSpec v AM M α Unit :=
  {
    to_AbstractREventSpec := ev.to_AbstractREventSpec
    event := ev.event
    step_ref := fun m x Hinv Hgrd _ => ev.step_ref m x Hinv Hgrd
    step_safe := fun m x Hinv Hgrd _ => ev.step_safe m x Hinv Hgrd
    lift_unlift := ev.lift_unlift
  }

@[simp]
def newAbstractConvergentRNDEvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : AbstractConvergentRNDEventSpec' v AM M α) : ConvergentRNDEvent v AM M α Unit :=
  newAbstractConvergentRNDEvent abs.toAbstractConvergentRNDEventSpec

structure AbstractConvergentRNDEventSpec''
              (v) [Preorder v] [WellFoundedLT v]
              (AM) [Machine ACTX AM]
              (M) [Machine CTX M]
              [Refinement AM M]
          extends _AbstractREventSpec AM M Unit where

  event : ConvergentNDEvent v AM Unit Unit

  step_ref (m : M):
    Machine.invariant m
    → event.guard (lift m) ()
    → ∀ am', event.effect (lift m) () ((), am')
             → refine am' (unlift (lift m) am' m ())

  step_safe (m : M):
    Machine.invariant m
    → event.guard (lift m) ()
    → ∀ am', event.effect (lift m) () ((), am')
             → Machine.invariant (unlift (lift m) am' m ())

  lift_unlift (m : M) (am am' : AM):
    Machine.invariant m → Machine.invariant am'
    → lift (unlift am am' m ()) = am'

@[simp]
def AbstractConvergentRNDEventSpec''.toAbstractConvergentRNDEventSpec  [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : AbstractConvergentRNDEventSpec'' v AM M) : AbstractConvergentRNDEventSpec v AM M Unit Unit :=
  {
    to_AbstractREventSpec := ev.to_AbstractREventSpec
    event := ev.event
    step_ref := fun m _ Hinv Hgrd _ => ev.step_ref m Hinv Hgrd
    step_safe := fun m _ Hinv Hgrd _ => ev.step_safe m Hinv Hgrd
    lift_unlift := fun m am am' _ => ev.lift_unlift m am am'
  }

@[simp]
def newAbstractConvergentRNDEvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : AbstractConvergentRNDEventSpec'' v AM M) : ConvergentRNDEvent v AM M Unit Unit :=
  newAbstractConvergentRNDEvent abs.toAbstractConvergentRNDEventSpec
