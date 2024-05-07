
/-
  Reuse of abstract events
-/

import EventSystems.Refinement.Relational.Basic
import EventSystems.Refinement.Relational.Convergent

open Refinement

/-
 Q : is there a better way to ease the definition of abstract events ? -/

structure _AbstractREventSpec (AM) [Machine ACTX AM]
                              (M) [Machine CTX M]
                              [Refinement AM M] (α) where

  lift (m: M) : AM

  lift_ref (m : M):
    Machine.invariant m → refine (lift m) m

  refine_uniq (am am' : AM) (m : M):
    Machine.invariant m
    → refine am m → refine am' m
    → am = am'

  unlift (am am' : AM) (m : M) (x : α): M

structure AbstractREventSpec (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                            [Refinement AM M]
  {α β} (abstract : _Event AM α β)
          extends _AbstractREventSpec AM M α where

  step_ref (m : M) (x : α):
    Machine.invariant m
    → abstract.guard (lift m) x
    → let (_, am') := abstract.action (lift m) x
      refine am' (unlift (lift m) am' m x)

  step_safe (m : M) (x : α):
    Machine.invariant m
    → abstract.guard (lift m) x
    → let (_, am') := abstract.action (lift m) x
      Machine.invariant am' -- redundant but useful
      → Machine.invariant (unlift (lift m) am' m x)

@[simp]
def newAbstractREvent [Machine ACTX AM] [Machine CTX M] [instR:Refinement AM M]
  (abs : OrdinaryEvent AM α β) (ev : AbstractREventSpec AM M abs.to_Event) : OrdinaryREvent AM M α β :=
  { guard := fun (m : M) (x : α) => abs.guard (ev.lift m) x
    action := fun (m : M) (x : α) => let am := ev.lift m
                                     let (y, am') := abs.action am x
                                     (y, ev.unlift am am' m x)
    po := {
      safety := fun (m : M) (x : α) => by
        simp
        intros Hinv Hgrd
        have Href := ev.lift_ref m Hinv
        have Hainv := Refinement.refine_safe (ev.lift m) m Hinv Href
        have Hsafe := abs.po.safety (ev.lift m) x Hainv Hgrd
        apply ev.step_safe m x Hinv Hgrd Hsafe

      lift_in := id
      lift_out := id

      abstract := abs.to_Event

      strengthening := fun m x => by simp
                                     intros Hinv Hgrd am Href
                                     have Href' := ev.lift_ref m Hinv
                                     have Ham: am = ev.lift m := by
                                       apply ev.refine_uniq am (ev.lift m) m <;> assumption
                                     rw [Ham]
                                     assumption

      simulation := fun m x => by simp
                                  intros Hinv Hgrd am Href
                                  have Href' := ev.lift_ref m Hinv
                                  have Ham: am = ev.lift m := by
                                    apply ev.refine_uniq am (ev.lift m) m <;> assumption
                                  rw [Ham]
                                  constructor
                                  · simp
                                  apply ev.step_ref m x Hinv Hgrd
    }
  }

structure AbstractAnticipatedREventSpec
              (v) [Preorder v]
              (AM) [Machine ACTX AM]
              (M) [Machine CTX M]
              [Refinement AM M]
  {α β} (abstract : AnticipatedEvent v AM α β)
          extends AbstractREventSpec AM M abstract.to_Event where

  step_variant (m : M) (x : α):
    Machine.invariant m
    → abstract.guard (lift m) x
    → let (_, am') := abstract.action (lift m) x
      Machine.invariant am' -- redundant but useful
      → abstract.po.variant (lift (unlift (lift m) am' m x))
      = abstract.po.variant am'

@[simp]
def newAbstractAnticipatedREvent [Preorder v]
                                 [Machine ACTX AM]
                                 [Machine CTX M]
                                 [instR:Refinement AM M]
  (abs : AnticipatedEvent v AM α β) (ev : AbstractAnticipatedREventSpec v AM M abs) : AnticipatedREvent v AM M α β :=
  let oev := newAbstractREvent abs.toOrdinaryEvent ev.toAbstractREventSpec
  {
    to_Event := oev.to_Event
    po := {
      safety := oev.po.safety
      lift_in := oev.po.lift_in
      lift_out := oev.po.lift_out
      abstract := abs.to_Event
      strengthening := oev.po.strengthening
      simulation := oev.po.simulation

      variant := fun m => abs.po.variant (ev.lift m)

      nonIncreasing := fun m x => by
        simp
        intros Hinv Hgrd
        have Hinv' := Refinement.refine_safe (ev.lift m) m Hinv (ev.lift_ref m Hinv)
        have Hainv := abs.po.safety (ev.lift m) x Hinv' Hgrd
        have Hni := abs.po.nonIncreasing (ev.lift m) x Hinv' Hgrd
        simp at Hni
        have Hsv := ev.step_variant m x Hinv Hgrd Hainv
        simp [oev]
        rw [Hsv]
        assumption
    }
  }

structure AbstractConvergentREventSpec
              (v) [Preorder v] [WellFoundedLT v]
              (AM) [Machine ACTX AM]
              (M) [Machine CTX M]
              [Refinement AM M]
  {α β} (abstract : ConvergentEvent v AM α β)
          extends AbstractAnticipatedREventSpec v AM M abstract.toAnticipatedEvent where

@[simp]
def newAbstractConvergentREvent  [Preorder v] [WellFoundedLT v]
                                 [Machine ACTX AM]
                                 [Machine CTX M]
                                 [instR:Refinement AM M]
  (abs : ConvergentEvent v AM α β) (ev : AbstractConvergentREventSpec v AM M abs) : ConvergentREvent v AM M α β :=
  let oev := newAbstractAnticipatedREvent abs.toAnticipatedEvent ev.toAbstractAnticipatedREventSpec
  {
    to_Event := oev.to_Event
    po := {
      safety := oev.po.safety
      lift_in := oev.po.lift_in
      lift_out := oev.po.lift_out
      abstract := abs.to_Event
      strengthening := oev.po.strengthening
      simulation := oev.po.simulation
      variant := oev.po.variant
      nonIncreasing := oev.po.nonIncreasing

      convergence := fun m x => by
        simp [oev]
        intros Hinv Hgrd
        have Hinv' := Refinement.refine_safe (ev.lift m) m Hinv (ev.lift_ref m Hinv)
        have Hainv := abs.po.safety (ev.lift m) x Hinv' Hgrd
        have Hcv := abs.po.convergence (ev.lift m) x Hinv' Hgrd
        simp at Hcv
        have Hsv := ev.step_variant m x Hinv Hgrd Hainv
        simp at Hsv
        rw [Hsv]
        assumption
    }
  }
