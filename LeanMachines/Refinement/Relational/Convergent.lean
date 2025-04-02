import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary
import LeanMachines.Event.Convergent
import LeanMachines.Refinement.Relational.Basic
import LeanMachines.Refinement.Relational.Ordinary


open Refinement


-- ### Anticipated transitionnal events


structure AnticipatedREvent (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR : Refinement AM M] [Preorder v]
  {α β α' β'} (abs : OrdinaryEvent AM α' β') extends AnticipatedEvent v M α β, OrdinaryREvent AM M abs where

-- There can be a refinement of an ordinary event by an anticipated one
instance [Machine ACTX AM] [Machine CTX M] [instR : Refinement AM M] [Preorder v]
  (abs : OrdinaryEvent AM α' β') (ev : AnticipatedREvent AM M abs (v := v)) :
    SafeREventPO
      (AM := AM) (M := M)
      (α := α) (β := β)
      (ev.toEvent (M := M)) (abs.toEvent (M := AM))
      (instSafeAbs := (instSafeEventPO_OrdinaryEvent abs))
      (instSafeEv := (instAnticipatedEventPO_AnticipatedEvent ev.toAnticipatedEvent).toSafeEventPO)
      (valid_kind := by simp)
  where
    lift_in := ev.lift_in
    lift_out := ev.lift_out
    strengthening := ev.strengthening
    simulation := ev.simulation

-- There can be a refinement of an anticipated event by an anticipated one
instance [Machine ACTX AM] [Machine CTX M] [instR : Refinement AM M] [Preorder v'] [Preorder v]
  (abs : AnticipatedEvent v' AM α' β') (ev : AnticipatedREvent AM M abs.toOrdinaryEvent (v := v)) :
    SafeREventPO
      (AM := AM) (M := M)
      (α := α) (β := β)
      (ev.toEvent (M := M)) (abs.toEvent (M := AM))
      (instSafeAbs := (instAnticipatedEventPO_AnticipatedEvent abs).toSafeEventPO)
      (instSafeEv := (instAnticipatedEventPO_AnticipatedEvent ev.toAnticipatedEvent).toSafeEventPO)
      (valid_kind := by simp)
  where
    lift_in := ev.lift_in
    lift_out := ev.lift_out
    strengthening := ev.strengthening
    simulation := ev.simulation

/-- Smart constructor for anticipated refined event (and its alternative versions with Unit as input/output types),
with: `abs` the (ordinary) event to refine, and
  `ev` the refined event specification (cf. `REventSpec`).
-/
@[simp]
def newAnticipatedREvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (abs : OrdinaryEvent AM α' β') [Preorder v]
  (ev: AnticipatedREvent AM M abs (α := α) (β := β) (v := v))
  : AnticipatedREvent AM M abs (α := α) (β := β) (v := v):= ev



structure AnticipatedREvent' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR : Refinement AM M] [Preorder v]
  {α α'} (abs : OrdinaryEvent AM α' Unit) extends AnticipatedEvent' v M α, OrdinaryREvent' AM M abs where


instance {α} [Machine CTX M] [Machine ACTX AM] [Refinement AM M] [Preorder v] (abs : OrdinaryEvent AM α' Unit) :
  Coe (AnticipatedREvent' (α := α) (v := v) AM M abs) (AnticipatedREvent (v := v) AM M (α := α) (β := Unit) abs) where
  coe ev := {
              lift_in := ev.lift_in
              lift_out := fun _ => ()
              strengthening := ev.strengthening
              simulation :=
              fun m x hinv hgrd am href =>
                by
                  simp
                  exact ev.simulation m x hinv hgrd am href
              guard := ev.guard
              action m x grd := ((), ev.action m x grd)
              safety := ev.safety
              variant := ev.variant
              nonIncreasing := ev.nonIncreasing
            }

@[simp]
def newAnticipatedREvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (abs : OrdinaryEvent AM α' Unit) [Preorder v]
  (ev: AnticipatedREvent' AM M abs (α := α) (v := v))
  : AnticipatedREvent AM M abs (α := α) (β := Unit) (v := v):= ev

structure AnticipatedREvent'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR : Refinement AM M] [Preorder v]
  (abs : OrdinaryEvent AM Unit Unit) extends AnticipatedEvent'' v M, OrdinaryREvent'' AM M abs where


instance[Machine CTX M] [Machine ACTX AM] [Refinement AM M] [Preorder v] (abs : OrdinaryEvent AM Unit Unit) :
  Coe (AnticipatedREvent'' (v := v) AM M abs) (AnticipatedREvent (v := v) AM M (α := Unit) (β := Unit) abs ) where
  coe ev := {
              lift_in := fun _ => ()
              lift_out := fun _ => ()
              strengthening m x:= ev.strengthening m
              simulation :=
              fun m x hinv hgrd am href =>
                by
                  simp
                  exact ev.simulation m hinv hgrd am href
              guard m x := ev.guard m
              action m x grd := ((), ev.action m grd)
              safety m x := ev.safety m
              variant := ev.variant
              nonIncreasing m x := ev.nonIncreasing m
            }

@[simp]
def newAnticipatedREvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (abs : OrdinaryEvent AM Unit Unit) [Preorder v]
  (ev: AnticipatedREvent'' AM M abs (v := v)) : AnticipatedREvent AM M abs (α := Unit) (β := Unit) (v := v):= ev


-- ### Convergent transitionnal events

structure ConvergentREvent (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR : Refinement AM M] [Preorder v] [WellFoundedLT v]
  {α β α' β'} (abs : OrdinaryEvent AM α' β') extends ConvergentEvent v M α β, OrdinaryREvent AM M abs


instance [Machine ACTX AM] [Machine CTX M] [instR : Refinement AM M] [Preorder v] [WellFoundedLT v]
  (abs : OrdinaryEvent AM α' β') (ev : ConvergentREvent AM M abs (v := v)) :
      SafeREventPO
      (AM := AM) (M := M)
      (α := α) (β := β)
      (ev.toEvent (M := M)) (abs.toEvent (M := AM))
      (instSafeAbs := instSafeEventPO_OrdinaryEvent abs)
      (instSafeEv := (instConvergentEventPO_ConvergentEvent ev.toConvergentEvent).toSafeEventPO)
      (valid_kind := by simp)
    where
      lift_in := ev.lift_in
      lift_out := ev.lift_out
      strengthening := ev.strengthening
      simulation := ev.simulation


instance [Machine ACTX AM] [Machine CTX M] [instR : Refinement AM M] [Preorder v] [WellFoundedLT v] [Preorder v']
  (abs : AnticipatedEvent v' AM α' β') (ev : ConvergentREvent AM M abs.toOrdinaryEvent (v := v)) :
      SafeREventPO
      (AM := AM) (M := M)
      (α := α) (β := β)
      (ev.toEvent (M := M)) (abs.toEvent (M := AM))
      (instSafeAbs := (instAnticipatedEventPO_AnticipatedEvent abs).toSafeEventPO)
      (instSafeEv := (instConvergentEventPO_ConvergentEvent ev.toConvergentEvent).toSafeEventPO)
      (valid_kind := by simp)
    where
      lift_in := ev.lift_in
      lift_out := ev.lift_out
      strengthening := ev.strengthening
      simulation := ev.simulation

instance [Machine ACTX AM] [Machine CTX M] [instR : Refinement AM M] [Preorder v] [WellFoundedLT v] [Preorder v'] [WellFoundedLT v']
  (abs : ConvergentEvent v' AM α' β') (ev : ConvergentREvent AM M abs.toOrdinaryEvent (v := v)) :
      SafeREventPO
      (AM := AM) (M := M)
      (α := α) (β := β)
      (ev.toEvent (M := M)) (abs.toEvent (M := AM))
      (instSafeAbs := (instConvergentEventPO_ConvergentEvent abs).toSafeEventPO)
      (instSafeEv := (instConvergentEventPO_ConvergentEvent ev.toConvergentEvent).toSafeEventPO)
      (valid_kind := by simp)
    where
      lift_in := ev.lift_in
      lift_out := ev.lift_out
      strengthening := ev.strengthening
      simulation := ev.simulation

/-- Smart constructor for anticipated refined event (and its alternative versions with Unit as input/output types),
with: `abs` the (ordinary) event to refine, and
  `ev` the refined event specification (cf. `REventSpec`).
-/
@[simp]
def newConvergentREvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (abs : OrdinaryEvent AM α' β') [Preorder v] [WellFoundedLT v]
  (ev: ConvergentREvent AM M abs (α := α) (β := β) (v := v))
  : ConvergentREvent AM M abs (α := α) (β := β) (v := v):= ev


structure ConvergentREvent' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR : Refinement AM M] [Preorder v] [WellFoundedLT v]
  {α α'} (abs : OrdinaryEvent AM α' Unit) extends ConvergentEvent' v M α, OrdinaryREvent' AM M abs where


instance {α} [Machine CTX M] [Machine ACTX AM] [Refinement AM M] [Preorder v] [WellFoundedLT v] (abs : OrdinaryEvent AM α' Unit) :
  Coe (ConvergentREvent' (α := α) (v := v) AM M abs) (ConvergentREvent (v := v) AM M (α := α) (β := Unit) abs ) where
  coe ev := {
              lift_in := ev.lift_in
              lift_out := fun _ => ()
              strengthening := ev.strengthening
              simulation :=
              fun m x hinv hgrd am href =>
                by
                  simp
                  exact ev.simulation m x hinv hgrd am href
              guard := ev.guard
              action m x grd := ((), ev.action m x grd)
              safety := ev.safety
              variant := ev.variant
              convergence := ev.convergence
            }

@[simp]
def newConvergentREvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (abs : OrdinaryEvent AM α' Unit) [Preorder v][WellFoundedLT v]
  (ev: ConvergentREvent' AM M abs (α := α) (v := v))
  : ConvergentREvent AM M abs (α := α) (β := Unit) (v := v):= ev

structure ConvergentREvent'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR : Refinement AM M] [Preorder v][WellFoundedLT v]
  (abs : OrdinaryEvent AM Unit Unit) extends ConvergentEvent'' v M, OrdinaryREvent'' AM M abs where


instance[Machine CTX M] [Machine ACTX AM] [Refinement AM M] [Preorder v] [WellFoundedLT v] (abs : OrdinaryEvent AM Unit Unit) :
  Coe (ConvergentREvent'' (v := v) AM M abs) (ConvergentREvent (v := v) AM M (α := Unit) (β := Unit) abs ) where
  coe ev := {
              lift_in := fun _ => ()
              lift_out := fun _ => ()
              strengthening m x:= ev.strengthening m
              simulation :=
              fun m x hinv hgrd am href =>
                by
                  simp
                  exact ev.simulation m hinv hgrd am href
              guard m x := ev.guard m
              action m x grd := ((), ev.action m grd)
              safety m x := ev.safety m
              variant := ev.variant
              convergence m x := ev.convergence m
            }

@[simp]
def newConvergentREvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (abs : OrdinaryEvent AM Unit Unit) [Preorder v] [WellFoundedLT v]
  (ev: ConvergentREvent'' AM M abs (v := v)) : ConvergentREvent AM M abs (α := Unit) (β := Unit) (v := v):= ev
