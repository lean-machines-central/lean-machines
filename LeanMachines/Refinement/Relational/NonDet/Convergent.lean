
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



/-- Variant of `AnticipatedRNDEvent` with implicit `Unit` output type -/


structure AnticipatedRNDEvent' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  (α) (α':=α)  (abs : OrdinaryNDEvent AM α' Unit)
  extends AnticipatedNDEvent' v M α,
          OrdinaryRNDEvent' AM M abs α where


instance {α} (v) [Preorder v] [Machine CTX M] [Machine ACTX AM] [Refinement AM M]
  (abs : OrdinaryNDEvent AM α' Unit) :
  Coe (AnticipatedRNDEvent' v AM M α α' abs) (AnticipatedRNDEvent v AM M  α Unit α' Unit abs) where
  coe ev := {
              lift_in := ev.lift_in
              lift_out := fun _ => ()
              strengthening := ev.strengthening
              simulation m x hinv grd _ m' := ev.simulation m x hinv grd m'
              guard := ev.guard
              effect m x grd ym' := ev.effect m x grd ym'.2
              safety m x hinv hgrd _ m' := ev.safety m x hinv hgrd m'
              feasibility m x hinv grd := ⟨(), ev.feasibility m x hinv grd⟩
              variant := ev.variant
              nonIncreasing m x hinv grd _ m' := ev.nonIncreasing m x hinv grd m'
            }

@[simp]
def newAnticipatedFromOrdinaryRNDEvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M] [Preorder v]
  (abs : OrdinaryNDEvent AM α' Unit)
  (ev: AnticipatedRNDEvent' AM M α (v := v) α' abs)
  : AnticipatedRNDEvent' AM M α (v := v) α' abs:= ev

def newAnticipatedFromAnticipatedRNDEvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M] [Preorder v'] [Preorder v]
  (abs : AnticipatedNDEvent v' AM α' Unit)
  (ev: AnticipatedRNDEvent' AM M  (α := α)  (v := v) α'  abs.toOrdinaryNDEvent)
  : AnticipatedRNDEvent' AM M  (α := α)  (v := v) α' abs.toOrdinaryNDEvent:= ev


/-- Variant of `AnticipatedRNDEvent` with implicit `Unit` input/output type -/


structure AnticipatedRNDEvent'' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit)
  extends AnticipatedNDEvent'' v M,
          OrdinaryRNDEvent'' AM M abs where


instance (v) [Preorder v] [Machine CTX M] [Machine ACTX AM] [Refinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit) :
  Coe (AnticipatedRNDEvent'' v AM M abs) (AnticipatedRNDEvent v AM M  Unit Unit Unit Unit abs) where
  coe ev := {
              lift_in := fun _ => ()
              lift_out := fun _ => ()
              strengthening m _ := ev.strengthening m
              simulation m _ hinv grd _ m' := ev.simulation m hinv grd m'
              guard m _ := ev.guard m
              effect m _ grd ym' := ev.effect m grd ym'.2
              safety m _ hinv hgrd _ m' := ev.safety m hinv hgrd m'
              feasibility m _ hinv grd := ⟨(), ev.feasibility m hinv grd⟩
              variant := ev.variant
              nonIncreasing m _ hinv grd _ m' := ev.nonIncreasing m hinv grd m'
            }

@[simp]
def newAnticipatedFromOrdinaryRNDEvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M] [Preorder v]
  (abs : OrdinaryNDEvent AM Unit Unit)
  (ev: AnticipatedRNDEvent'' AM M  (v := v)  abs)
  : AnticipatedRNDEvent'' AM M  (v := v)  abs:= ev

def newAnticipatedFromAnticipatedRNDEvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M] [Preorder v'] [Preorder v]
  (abs : AnticipatedNDEvent v' AM Unit Unit)
  (ev: AnticipatedRNDEvent'' AM M    (v := v)   abs.toOrdinaryNDEvent)
  : AnticipatedRNDEvent'' AM M  (v := v)  abs.toOrdinaryNDEvent:= ev






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


/-!
  Variant of `ConvergentRNDEvent` with implicit `Unit` output type
-/


structure ConvergentRNDEvent' (v) [Preorder v] [WellFoundedLT v]
  (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  (α) (α':=α) (abs : OrdinaryNDEvent AM α' Unit)
  extends ConvergentNDEvent' v M α ,
          OrdinaryRNDEvent' AM M abs α where

instance {α} (v) [Preorder v] [WellFoundedLT v] [Machine CTX M] [Machine ACTX AM] [Refinement AM M]
  (abs : OrdinaryNDEvent AM α' Unit) :
  Coe (ConvergentRNDEvent' v AM M α α' abs) (ConvergentRNDEvent v AM M  α Unit α' Unit abs) where
  coe ev := {
              lift_in := ev.lift_in
              lift_out := fun _ => ()
              strengthening := ev.strengthening
              simulation m x hinv grd _ m' := ev.simulation m x hinv grd m'
              guard := ev.guard
              effect m x grd ym' := ev.effect m x grd ym'.2
              safety m x hinv hgrd _ m' := ev.safety m x hinv hgrd m'
              feasibility m x hinv grd := ⟨(), ev.feasibility m x hinv grd⟩
              variant := ev.variant
              convergence m x hinv hgrd _ m' := ev.convergence m x hinv hgrd m'
            }

@[simp]
def newConvergentFromOrdinaryRNDEvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   [Preorder v] [WellFoundedLT v]
  (abs : OrdinaryNDEvent AM α' Unit)
  (ev: ConvergentRNDEvent' AM M α  (v := v) α'  abs)
  : ConvergentRNDEvent' AM M α  (v := v) α' abs:= ev

def newConvergentFromAnticipatedRNDEvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   [Preorder v'] [Preorder v] [WellFoundedLT v]
  (abs : AnticipatedNDEvent v' AM α' Unit)
  (ev: ConvergentRNDEvent' AM M  (α := α)  (v := v) α'  abs.toOrdinaryNDEvent)
  : ConvergentRNDEvent' AM M  (α := α)  (v := v) α'  abs.toOrdinaryNDEvent:= ev

def newConvergentFromConvergentRNDEvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   [Preorder v'] [Preorder v] [WellFoundedLT v]  [WellFoundedLT v']
  (abs : ConvergentNDEvent v' AM α' Unit)
  (ev: ConvergentRNDEvent' AM M  (α := α)  (v := v) α' abs.toOrdinaryNDEvent)
  : ConvergentRNDEvent' AM M  (α := α)  (v := v) α'  abs.toOrdinaryNDEvent:= ev


/-!
  Variant of `ConvergentRNDEvent` with implicit `Unit` input/output type
-/


structure ConvergentRNDEvent'' (v) [Preorder v] [WellFoundedLT v]
  (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit)
  extends ConvergentNDEvent'' v M  ,
          OrdinaryRNDEvent'' AM M abs where

instance  (v) [Preorder v] [WellFoundedLT v] [Machine CTX M] [Machine ACTX AM] [Refinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit) :
  Coe (ConvergentRNDEvent'' v AM M  abs) (ConvergentRNDEvent v AM M  Unit Unit Unit Unit abs) where
  coe ev := {
              lift_in := fun _ => ()
              lift_out := fun _ => ()
              strengthening m _ := ev.strengthening m
              simulation m _ hinv grd _ m' := ev.simulation m  hinv grd m'
              guard m _ := ev.guard m
              effect m _ grd ym' := ev.effect m  grd ym'.2
              safety m _ hinv hgrd _ m' := ev.safety m  hinv hgrd m'
              feasibility m _ hinv grd := ⟨(), ev.feasibility m  hinv grd⟩
              variant := ev.variant
              convergence m _ hinv hgrd _ m' := ev.convergence m  hinv hgrd m'
            }

@[simp]
def newConvergentFromOrdinaryRNDEvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   [Preorder v] [WellFoundedLT v]
  (abs : OrdinaryNDEvent AM Unit Unit)
  (ev: ConvergentRNDEvent'' AM M   (v := v)   abs)
  : ConvergentRNDEvent'' AM M   (v := v)  abs:= ev

def newConvergentFromAnticipatedRNDEvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   [Preorder v'] [Preorder v] [WellFoundedLT v]
  (abs : AnticipatedNDEvent v' AM Unit Unit)
  (ev: ConvergentRNDEvent'' AM M   (v := v)   abs.toOrdinaryNDEvent)
  : ConvergentRNDEvent'' AM M   (v := v)   abs.toOrdinaryNDEvent:= ev

def newConvergentFromConvergentRNDEvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   [Preorder v'] [Preorder v] [WellFoundedLT v]  [WellFoundedLT v']
  (abs : ConvergentNDEvent v' AM Unit Unit)
  (ev: ConvergentRNDEvent'' AM M    (v := v)  abs.toOrdinaryNDEvent)
  : ConvergentRNDEvent'' AM M    (v := v)   abs.toOrdinaryNDEvent:= ev
