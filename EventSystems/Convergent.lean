
import Mathlib.Order.RelClasses

import EventSystems.Basic

/- Anticipated events -/

structure _AnticipatedEventPO (v) [Preorder v] [Machine CTX M] (ev : _Event M α β) (kind : EventKind)
          extends _EventPO ev kind  where

  variant : M → v

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → let (_, m') := ev.action m x
      variant m' ≤ variant m

structure AnticipatedEvent (v) [Preorder v] (M) [Machine CTX M] (α) (β)
          extends (_Event M α β)  where
  po : _AnticipatedEventPO v to_Event (EventKind.TransDet Convergence.Anticipated)

structure AnticipatedEventSpec (v) [Preorder v] {CTX} (M) [Machine CTX M] (α) (β)
  extends EventSpec M α β where
  variant : M → v
  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := (action m x).2
      variant m' ≤ variant m

@[simp]
def newAnticipatedEvent {v} [Preorder v] {M} [Machine CTX M] (ev : AnticipatedEventSpec v M α β) : AnticipatedEvent v M α β :=
  let event := _Event_from_EventSpec ev.toEventSpec
  { guard := event.guard
    action := event.action
    po := { safety := fun m x => by simp
                                    intros Hinv Hgrd
                                    apply ev.safety <;> assumption
            variant := ev.variant
            nonIncreasing:= fun m x => by simp
                                          intros Hinv Hgrd
                                          apply ev.nonIncreasing <;> assumption
    }
  }
