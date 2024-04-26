
import EventSystems.NonDet.Ordinary
import EventSystems.Refinement.Relational.NonDet.Basic
import EventSystems.Refinement.Relational.Abstract

open Refinement

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

  step_unlift (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → ∀ y, ∀ m', event.effect (lift m) x (y, lift m')
                  → Machine.invariant (unlift (lift m) (lift m') m x)
                  → Machine.invariant m'

  lift_unlift (m : M) (am am' : AM) (x : α):
    Machine.invariant m → Machine.invariant am'
    → lift (unlift am am' m x) = am'


@[simp]
def newAbstractRNDEvent [Machine ACTX AM] [Machine CTX M] [instR:Refinement AM M]
  (abs : AbstractRNDEventSpec AM M α β) : OrdinaryRNDEvent AM M α β :=
  {
    guard := fun m x => abs.event.guard (abs.lift m) x
    effect := fun m x (y, m') => abs.event.effect (abs.lift m) x (y, abs.lift m')
    po := {
      safety := fun m x => by
        simp
        intros Hinv Hgrd y m' Heff
        have Href := abs.lift_ref m Hinv
        have Hainv := refine_safe (abs.lift m) m Hinv Href
        have Hainv' := abs.event.po.safety (abs.lift m) x Hainv Hgrd y (abs.lift m') Heff
        have Hssafe := abs.step_safe m x Hinv Hgrd y (abs.lift m') Heff
        have Hsunlift := abs.step_unlift m x Hinv Hgrd y m' Heff Hssafe
        exact Hsunlift

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
        assumption

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
        intros Hinv Hagrd y m' Heff am Href
        exists (abs.lift m')
        constructor
        · have Href' := abs.lift_ref m Hinv
          have Huniq := abs.refine_uniq am (abs.lift m) m Hinv Href Href'
          rw [Huniq]
          exact Heff
        have Hsafe' : Machine.invariant m' := by
          have Href := abs.lift_ref m Hinv
          have Hainv := refine_safe (abs.lift m) m Hinv Href
          have Hainv' := abs.event.po.safety (abs.lift m) x Hainv Hagrd y (abs.lift m') Heff
          have Hssafe := abs.step_safe m x Hinv Hagrd y (abs.lift m') Heff
          have Hsunlift := abs.step_unlift m x Hinv Hagrd y m' Heff Hssafe
          exact Hsunlift
          -- this is the safety proof ! (need to reuse)
        apply abs.lift_ref ; assumption
    }
  }
