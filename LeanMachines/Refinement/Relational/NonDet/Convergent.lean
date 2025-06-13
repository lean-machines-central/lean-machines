
import LeanMachines.NonDet.Basic
import LeanMachines.NonDet.Convergent
import LeanMachines.Refinement.Relational.NonDet.Basic
import LeanMachines.Refinement.Relational.NonDet.Ordinary

/-!

# Convergent refined non-deterministic events

This module defines the construction of anticipated and
convergent refind non-deterministic events.

-/

open Refinement

/-!
## Anticipated events
-/


structure AnticipatedRNDEvent (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  (α) (β) (α':=α) (β':=β) (abs : OrdinaryNDEvent AM α' β')
  extends AnticipatedNDEvent v M α β,
          OrdinaryRNDEvent AM M α β α' β' abs where


instance [Machine ACTX AM] [Machine CTX M] [instR : Refinement AM M] [Preorder v]
  (abs : OrdinaryNDEvent AM α' β') (ev : AnticipatedRNDEvent AM M (v := v) α β α' β' abs) :
    SafeRNDEventPO
      (ev.toNDEvent ) (abs.toNDEvent )
      (instSafeAbs := (instSafeNDEventPO_Ordinary abs))
      (instSafeEv := (instSafeNDEventPO_Anticipated ev.toAnticipatedNDEvent))
      (valid_kind := by simp)
  where
    lift_in := ev.lift_in
    lift_out := ev.lift_out
    strengthening := ev.strengthening
    simulation := ev.simulation


instance [Machine ACTX AM] [Machine CTX M] [instR : Refinement AM M] [Preorder v'] [Preorder v]
  (abs : AnticipatedNDEvent v' AM α' β') (ev : AnticipatedRNDEvent AM M (v := v) α β  α' β' abs.toOrdinaryNDEvent) :
    SafeRNDEventPO
      (ev.toNDEvent) (abs.toNDEvent)
      (instSafeAbs := (instSafeNDEventPO_Anticipated abs))
      (instSafeEv := (instSafeNDEventPO_Anticipated ev.toAnticipatedNDEvent))
      (valid_kind := by simp)
  where
    lift_in := ev.lift_in
    lift_out := ev.lift_out
    strengthening := ev.strengthening
    simulation := ev.simulation




@[simp]
def newAnticipatedFromOrdinaryRNDEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M] [Preorder v]
  (abs : OrdinaryNDEvent AM α' β')
  (ev: AnticipatedRNDEvent AM M α β (v := v) α' β' abs)
  : AnticipatedRNDEvent AM M α β (v := v) α' β' abs:= ev

def newAnticipatedFromAnticipatedRNDEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M] [Preorder v'] [Preorder v]
  (abs : AnticipatedNDEvent v' AM α' β')
  (ev: AnticipatedRNDEvent AM M  (α := α) (β := β) (v := v) α' β' abs.toOrdinaryNDEvent)
  : AnticipatedRNDEvent AM M  (α := α) (β := β) (v := v) α' β' abs.toOrdinaryNDEvent:= ev


/-!
### Convergent refined events
-/






structure ConvergentRNDEvent (v) [Preorder v] [WellFoundedLT v]
  (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  (α) (β) (α':=α) (β':=β) (abs : OrdinaryNDEvent AM α' β')
  extends ConvergentNDEvent v M α β,
          OrdinaryRNDEvent AM M α β α' β' abs where


instance [Machine ACTX AM] [Machine CTX M] [instR : Refinement AM M]
  [Preorder v] [WellFoundedLT v]
  (abs : OrdinaryNDEvent AM α' β') (ev : ConvergentRNDEvent AM M (v := v) α β α' β' abs) :
    SafeRNDEventPO
      (ev.toNDEvent ) (abs.toNDEvent )
      (instSafeAbs := instSafeNDEventPO_Ordinary abs)
      (instSafeEv := instSafeNDEventPO_Convergent ev.toConvergentNDEvent)
      (valid_kind := by simp)
  where
    lift_in := ev.lift_in
    lift_out := ev.lift_out
    strengthening := ev.strengthening
    simulation := ev.simulation

instance [Machine ACTX AM] [Machine CTX M] [instR : Refinement AM M]
  [Preorder v'] [Preorder v] [WellFoundedLT v]
  (abs : AnticipatedNDEvent v' AM α' β') (ev : ConvergentRNDEvent AM M (v := v) α β  α' β' abs.toOrdinaryNDEvent) :
    SafeRNDEventPO
      (ev.toNDEvent) (abs.toNDEvent)
      (instSafeAbs := (instSafeNDEventPO_Anticipated abs))
      (instSafeEv := instSafeNDEventPO_Convergent ev.toConvergentNDEvent)
      (valid_kind := by simp)
  where
    lift_in := ev.lift_in
    lift_out := ev.lift_out
    strengthening := ev.strengthening
    simulation := ev.simulation

instance [Machine ACTX AM] [Machine CTX M] [instR : Refinement AM M]
  [Preorder v'] [Preorder v] [WellFoundedLT v] [WellFoundedLT v']
  (abs : ConvergentNDEvent v' AM α' β') (ev : ConvergentRNDEvent AM M (v := v) α β  α' β' abs.toOrdinaryNDEvent) :
    SafeRNDEventPO
      (ev.toNDEvent) (abs.toNDEvent)
      (instSafeAbs := (instSafeNDEventPO_Convergent abs))
      (instSafeEv := instSafeNDEventPO_Convergent ev.toConvergentNDEvent)
      (valid_kind := by simp)
  where
    lift_in := ev.lift_in
    lift_out := ev.lift_out
    strengthening := ev.strengthening
    simulation := ev.simulation



@[simp]
def newConvergentFromOrdinaryRNDEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   [Preorder v] [WellFoundedLT v]
  (abs : OrdinaryNDEvent AM α' β')
  (ev: ConvergentRNDEvent AM M α β (v := v) α' β' abs)
  : ConvergentRNDEvent AM M α β (v := v) α' β' abs:= ev

def newConvergentFromAnticipatedRNDEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   [Preorder v'] [Preorder v] [WellFoundedLT v]
  (abs : AnticipatedNDEvent v' AM α' β')
  (ev: ConvergentRNDEvent AM M  (α := α) (β := β) (v := v) α' β' abs.toOrdinaryNDEvent)
  : ConvergentRNDEvent AM M  (α := α) (β := β) (v := v) α' β' abs.toOrdinaryNDEvent:= ev

def newConvergentFromConvergentRNDEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   [Preorder v'] [Preorder v] [WellFoundedLT v]  [WellFoundedLT v']
  (abs : ConvergentNDEvent v' AM α' β')
  (ev: ConvergentRNDEvent AM M  (α := α) (β := β) (v := v) α' β' abs.toOrdinaryNDEvent)
  : ConvergentRNDEvent AM M  (α := α) (β := β) (v := v) α' β' abs.toOrdinaryNDEvent:= ev
