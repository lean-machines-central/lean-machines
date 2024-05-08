
import EventSystems.NonDet.Ordinary
import EventSystems.Refinement.Relational.NonDet.Basic
import EventSystems.Refinement.Relational.NonDet.Convergent
import EventSystems.Refinement.Relational.Abstract

open Refinement

structure _AbstractRNDEventSpec (AM) [Machine ACTX AM]
                               (M) [Machine CTX M]
                               [Refinement AM M] (α)
          extends _AbstractREventSpec AM M α where

  lift_unlift (m : M) (am am' : AM) (x : α):
    Machine.invariant m → Machine.invariant am'
    → lift (unlift am am' m x) = am'


structure AbstractRNDEventSpec (AM) [Machine ACTX AM]
                               (M) [Machine CTX M]
                               [Refinement AM M]
  {α β} (abstract : _NDEvent AM α β)
          extends _AbstractRNDEventSpec AM M α where

  step_ref (m : M) (x : α):
    Machine.invariant m
    → abstract.guard (lift m) x
    → ∀ y, ∀ am', abstract.effect (lift m) x (y, am')
                  → refine am' (unlift (lift m) am' m x)

  step_safe (m : M) (x : α):
    Machine.invariant m
    → abstract.guard (lift m) x
    → ∀ y, ∀ am', abstract.effect (lift m) x (y, am')
                  → Machine.invariant (unlift (lift m) am' m x)

@[simp]
def newAbstractRNDEvent [Machine ACTX AM] [Machine CTX M] [instR:Refinement AM M]
  (abs : OrdinaryNDEvent AM α β) (ev : AbstractRNDEventSpec AM M abs.to_NDEvent) : OrdinaryRNDEvent AM M α β :=
  {
    guard := fun m x => abs.guard (ev.lift m) x
    effect := fun m x (y, m') => abs.effect (ev.lift m) x (y, ev.lift m')
                                 ∧ m' = ev.unlift (ev.lift m) (ev.lift m') m x
    po := {
      lift_in := id
      lift_out := id
      safety := fun m x => by
        simp
        intros Hinv Hagrd y m' Heff Hm'
        rw [Hm']
        apply ev.step_safe m x Hinv Hagrd y (ev.lift m') Heff

      feasibility := fun m x => by
        simp
        intros Hinv Hagrd
        have Href := ev.lift_ref m Hinv
        have Hainv := refine_safe (ev.lift m) m Hinv Href
        obtain ⟨y, am', Hafeas⟩ := abs.po.feasibility (ev.lift m) x Hainv Hagrd
        exists y
        exists (ev.unlift (ev.lift m) am' m x)
        have Hsref := ev.step_ref m x Hinv Hagrd y am' Hafeas
        have Hssafe := ev.step_safe m x Hinv Hagrd y am' Hafeas
        have Hasafe' := refine_safe am' (ev.unlift (ev.lift m) am' m x) Hssafe Hsref
        have Hlu := ev.lift_unlift m (ev.lift m) am' x Hinv Hasafe'
        rw [Hlu]
        simp [Hafeas]

      abstract := abs.to_NDEvent

      strengthening := fun m x => by
        simp
        intros Hinv Hagrd am Href
        have Href' := ev.lift_ref m Hinv
        have Huniq := ev.refine_uniq am (ev.lift m) m Hinv Href Href'
        rw [Huniq]
        exact Hagrd

      simulation := fun m x => by
        simp
        intros Hinv Hagrd y m' Heff Hm' am Href
        have Href' := ev.lift_ref m Hinv
        exists (ev.lift m')
        constructor
        · have Huniq := ev.refine_uniq am (ev.lift m) m Hinv Href Href'
          rw [Huniq]
          exact Heff
        -- and
        rw [Hm']
        rw [ev.lift_unlift]
        · apply ev.step_ref m x Hinv Hagrd y (ev.lift m') Heff
        · assumption
        -- finally
        have Hainv := refine_safe (ev.lift m) m Hinv Href'
        apply abs.po.safety (ev.lift m) x Hainv Hagrd y (ev.lift m') Heff
    }
  }

@[simp]
def newAbstractRNDEvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM α Unit) (ev : AbstractRNDEventSpec AM M abs.to_NDEvent) : OrdinaryRNDEvent AM M α Unit :=
  newAbstractRNDEvent abs ev

@[simp]
def newAbstractRNDEvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit) (ev : AbstractRNDEventSpec AM M abs.to_NDEvent) : OrdinaryRNDEvent AM M Unit Unit :=
  newAbstractRNDEvent abs ev

@[simp]
def newAbstractAnticipatedRNDEvent [Preorder v] [Machine ACTX AM] [Machine CTX M] [instR:Refinement AM M]
  (abs : AnticipatedNDEvent v AM α β) (ev : AbstractRNDEventSpec AM M abs.to_NDEvent) : AnticipatedRNDEvent v AM M α β :=
  let aev := newAbstractRNDEvent abs.toOrdinaryNDEvent ev
  {
    to_NDEvent := aev.to_NDEvent
    po := {
      safety :=aev.po.safety
      feasibility := aev.po.feasibility
      lift_in := aev.po.lift_in
      lift_out := aev.po.lift_out
      abstract := abs.to_NDEvent
      strengthening := aev.po.strengthening
      simulation := aev.po.simulation

      variant := fun m => abs.po.variant (ev.lift m)
      nonIncreasing := fun m x => by
        simp [aev]
        intros Hinv Hgrd y m' Heff _
        have Hinv' := Refinement.refine_safe (ev.lift m) m Hinv (ev.lift_ref m Hinv)
        apply abs.po.nonIncreasing (ev.lift m) x Hinv' Hgrd y (ev.lift m') Heff
    }
  }

@[simp]
def newAbstractAnticipatedRNDEvent' [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : AnticipatedNDEvent v AM α Unit) (ev : AbstractRNDEventSpec AM M abs.to_NDEvent) : AnticipatedRNDEvent v AM M α Unit :=
  newAbstractAnticipatedRNDEvent abs ev

@[simp]
def newAbstractAnticipatedRNDEvent'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : AnticipatedNDEvent v AM Unit Unit) (ev : AbstractRNDEventSpec AM M abs.to_NDEvent) : AnticipatedRNDEvent v AM M Unit Unit :=
  newAbstractAnticipatedRNDEvent abs ev

@[simp]
def newAbstractConvergentRNDEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instR:Refinement AM M]
  (abs : ConvergentNDEvent v AM α β) (ev : AbstractRNDEventSpec AM M abs.to_NDEvent) : ConvergentRNDEvent v AM M α β :=
  let aev := newAbstractAnticipatedRNDEvent abs.toAnticipatedNDEvent ev
  {
    to_NDEvent := aev.to_NDEvent
    po := {
      safety :=aev.po.safety
      feasibility := aev.po.feasibility
      lift_in := aev.po.lift_in
      lift_out := aev.po.lift_out
      abstract := abs.to_NDEvent
      strengthening := aev.po.strengthening
      simulation := aev.po.simulation
      variant := aev.po.variant
      nonIncreasing := aev.po.nonIncreasing
      convergence := fun m x => by
        simp [aev]
        intros Hinv Hgrd y m' Heff _
        have Hinv' := Refinement.refine_safe (ev.lift m) m Hinv (ev.lift_ref m Hinv)
        apply abs.po.convergence (ev.lift m) x Hinv' Hgrd y (ev.lift m') Heff
    }
  }

@[simp]
def newAbstractConvergentRNDEvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : ConvergentNDEvent v AM α Unit) (ev : AbstractRNDEventSpec AM M abs.to_NDEvent) : ConvergentRNDEvent v AM M α Unit :=
  newAbstractConvergentRNDEvent abs ev

@[simp]
def newAbstractConvergentRNDEvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : ConvergentNDEvent v AM Unit Unit) (ev : AbstractRNDEventSpec AM M abs.to_NDEvent) : ConvergentRNDEvent v AM M Unit Unit :=
  newAbstractConvergentRNDEvent abs ev
