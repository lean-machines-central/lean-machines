
/-
  Reuse of abstract events
-/

import EventSystems.Refinement.Basic

open Refinement

/-
 Q : is there a better way to ease the definition of abstract events ? -/
structure AbstractREventSpec {ACTX} (AM) [Machine ACTX AM]
                               {CTX} (M) [Machine CTX M]
                               [Refinement AM M] (α) (β) where

  event : OrdinaryEvent AM α β

  lift (m: M) (x: α) : AM

  lift_ref (m : M) (x : α):
    Machine.invariant m → refine (lift m x) m

  refine_uniq (am am' : AM) (m : M):
    Machine.invariant m
    → refine am m → refine am' m
    → am = am'

  unlift (am am' : AM) (m : M) (x : α): M

  step_ref (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m x) x
    → let (_, am') := event.action (lift m x) x
      refine am' (unlift (lift m x) am' m x)

  step_safe (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m x) x
    → let (_, am') := event.action (lift m x) x
      Machine.invariant am' -- redundant but useful
      → Machine.invariant (unlift (lift m x) am' m x)

@[simp]
def newAbstractREvent {ACTX} {AM} [Machine ACTX AM]
                       {CTX} {M} [Machine CTX M]
                       [instR:Refinement AM M]
  (abs : AbstractREventSpec AM M α β) : OrdinaryREvent AM M α β :=
  { guard := fun (m : M) (x : α) => abs.event.guard (abs.lift m x) x
    action := fun (m : M) (x : α) => let am := abs.lift m x
                                     let (y, am') := abs.event.action am x
                                     (y, abs.unlift am am' m x)
    po := {
      safety := fun (m : M) (x : α) => by
        simp
        intros Hinv Hgrd
        have Href := abs.lift_ref m x Hinv
        have Hainv := Refinement.refine_safe (abs.lift m x) m Hinv Href
        have Hsafe := abs.event.po.safety (abs.lift m x) x Hainv Hgrd
        apply abs.step_safe m x Hinv Hgrd Hsafe

      abstract := abs.event.to_Event

      strengthening := fun m x => by simp
                                     intros Hinv Hgrd am Href
                                     have Href' := abs.lift_ref m x Hinv
                                     have Ham: am = abs.lift m x := by
                                       apply abs.refine_uniq am (abs.lift m x) m <;> assumption
                                     rw [Ham]
                                     assumption

      simulation := fun m x => by simp
                                  intros Hinv Hgrd am Href
                                  have Href' := abs.lift_ref m x Hinv
                                  have Ham: am = abs.lift m x := by
                                    apply abs.refine_uniq am (abs.lift m x) m <;> assumption
                                  rw [Ham]
                                  constructor
                                  · simp
                                  apply abs.step_ref m x Hinv Hgrd
    }
  }
