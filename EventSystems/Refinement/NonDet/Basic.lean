
import EventSystems.NonDet.Basic
import EventSystems.Refinement.Basic

open Refinement

structure _RNDEventPO  [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
   (ev : _NDEvent M α β) (kind : EventKind)
   extends _NDEventPO ev kind where

  abstract : _NDEvent AM α β

  strengthening (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → ∀ am, refine am m
      → abstract.guard am x

  simulation (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → ∀ y, ∀ m', ev.effect m x (y, m')
      -- XXX : some constraint on output ?
      → ∀ am, refine am m
        → ∃ z, ∃ am', abstract.effect am x (z, am')
                      → y = z ∧ refine am' m'

structure OrdinaryRNDEvent (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M] (α) (β) extends _NDEvent M α β where
  po : _RNDEventPO (instR:=instR) to_NDEvent (EventKind.TransNonDet Convergence.Ordinary)

structure RNDEventSpec {ACTX} (AM) [Machine ACTX AM]
                        {CTX} (M) [Machine CTX M]
                        [Refinement AM M] (α) (β)
  extends NDEventSpec M α β where

  abstract : OrdinaryNDEvent AM α β

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ am, refine am m
      → abstract.guard am x

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ y, ∀ m', effect m x (y, m')
      -- XXX : some constraint on output ?
      → ∀ am, refine am m
        → ∃ z, ∃ am', abstract.effect am x (z, am')
                      → y = z ∧ refine am' m'

@[simp]
def newRNDEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : RNDEventSpec AM M α β) : OrdinaryRNDEvent AM M α β :=
  let event := _NDEvent_from_NDEventSpec ev.toNDEventSpec
  { guard := event.guard
    effect := event.effect
    po := { safety := fun m x => by simp
                                    intros Hinv Hgrd
                                    apply ev.safety <;> assumption
            feasibility := fun m x => by simp
                                         intros Hinv Hgrd
                                         apply ev.feasibility <;> assumption
            abstract := ev.abstract.to_NDEvent
            strengthening := ev.strengthening
            simulation := ev.simulation
    }
  }

structure InitRNDEventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M] (α) (β)
  extends InitNDEventSpec M α β where

  abstract : OrdinaryNDEvent AM α β

  strengthening (x : α):
    guard x
    → abstract.guard Machine.reset x

  simulation (x : α):
    guard x
    → ∀ y, ∀ m', init x (y, m')
      -- XXX : some constraint on output ?
      → ∃ z, ∃ am', abstract.effect Machine.reset x (z, am')
                    → y = z ∧ refine am' m'

def RNDEventSpec_from_InitRNDEventSpec [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : InitRNDEventSpec AM M α β) : RNDEventSpec AM M α β :=
  {
    guard := fun m x => m = Machine.reset ∧ ev.guard x
    effect := fun _ x (y,m') => ev.init x (y, m')
    safety := fun m x => by intro _ ⟨_, Hgrd⟩
                            intros y m' Hinit
                            simp at Hinit
                            apply ev.safety x Hgrd y m' Hinit
    feasibility := fun m x => by simp
                                 intros _ _ Hgrd
                                 have Hfeas := ev.feasibility x Hgrd
                                 obtain ⟨y,m', Hini⟩ := Hfeas
                                 exists y
                                 exists m'
    abstract := ev.abstract
    strengthening := fun m x => by simp
                                   intros _ Hrst Hgrd am Href
                                   rw [Hrst] at Href
                                   have Hax := refine_reset am Href
                                   rw [Hax]
                                   apply ev.strengthening x Hgrd
    simulation := fun m x => by simp
                                intros _ Hrst Hgrd y m' Hini am Href
                                have Hsim := ev.simulation x Hgrd y m' Hini
                                obtain ⟨z, am', Habs⟩ := Hsim
                                exists z ; exists am'
                                rw [Hrst] at Href
                                have Hax := refine_reset am Href
                                rw [Hax]
                                exact Habs
  }

@[simp]
def newInitRNDEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : InitRNDEventSpec AM M α β) : OrdinaryRNDEvent AM M α β :=
  newRNDEvent (RNDEventSpec_from_InitRNDEventSpec ev)
