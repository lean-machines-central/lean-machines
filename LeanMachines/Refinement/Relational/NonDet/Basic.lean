import LeanMachines.NonDet.Basic
import LeanMachines.NonDet.Ordinary
import LeanMachines.Refinement.Relational.Basic

open Refinement
/-!

# Relational refinement of Non-deterministic events

This module contains the principles of relational refinement
for ordinary, non-deterministic events.

-/

/-!
## Ordinary non-deterministic events
-/


/-
  This typeclass specifies the proof obligations for the refinement of events.
-/
class SafeRNDEventPO {α β α' β'} [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : NDEvent M α β) (abs : NDEvent AM α' β') [instSafeAbs : SafeNDEventPO abs kabs] [instSafeEv : SafeNDEventPO ev kev]
  {valid_kind : kev.canRefine? kabs = true} where

  lift_in : α → α'
  lift_out : β → β'

  strengthening (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → ∀ am, refine am m
      → abs.guard am (lift_in x)

  simulation (m : M) (x : α):
    (Hinv : Machine.invariant m)
    → (Hgrd : ev.guard m x)
    → ∀ y, ∀ m', ev.effect m x Hgrd (y, m')
      → ∀ am, (Href : refine am m)
        → ∃ am', abs.effect am (lift_in x) (strengthening m x Hinv Hgrd am Href) (lift_out y, am')
                 ∧ refine am' m'


structure OrdinaryRNDEvent (AM) [Machine ACTX AM] (M) [Machine CTX M]
  [instR : Refinement AM M]   {α' β'} (abs : OrdinaryNDEvent AM α' β') (α) (β)
  extends OrdinaryNDEvent M α β where

  lift_in : α → α'
  lift_out : β → β'

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ am, refine am m
      → abs.guard am (lift_in x)

  simulation (m : M) (x : α):
    (Hinv : Machine.invariant m)
    → (Hgrd : guard m x)
    → ∀ y, ∀ m', effect m x Hgrd (y, m')
      → ∀ am, (Href : refine am m)
        → ∃ am', abs.effect am (lift_in x) (strengthening m x Hinv Hgrd am Href) (lift_out y, am')
                 ∧ refine am' m'


instance [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (abs : OrdinaryNDEvent AM α' β') (ev : OrdinaryRNDEvent AM M abs α β):
  SafeRNDEventPO
    (ev.toNDEvent) (abs.toNDEvent)
    (instSafeAbs :=instSafeNDEventPO_Ordinary abs)
    (instSafeEv := instSafeNDEventPO_Ordinary ev.toOrdinaryNDEvent)
    (valid_kind := by simp)
where
  lift_in := ev.lift_in
  lift_out := ev.lift_out
  strengthening := ev.strengthening
  simulation := ev.simulation


@[simp]
def newRNDEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM α' β')
  (ev: OrdinaryRNDEvent AM M abs α β)
  : OrdinaryRNDEvent AM M abs α β := ev


  structure OrdinaryRNDEvent' (AM) [Machine ACTX AM] (M) [Machine CTX M]
  [instR : Refinement AM M]   {α'} (abs : OrdinaryNDEvent AM α' Unit) (α)
  extends OrdinaryNDEvent M α Unit where

  lift_in : α → α'

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ am, refine am m
      → abs.guard am (lift_in x)

  simulation (m : M) (x : α):
    (Hinv : Machine.invariant m)
    → (Hgrd : guard m x)
    → ∀ y, ∀ m', effect m x Hgrd (y, m')
      → ∀ am, (Href : refine am m)
        → ∃ am', abs.effect am (lift_in x) (strengthening m x Hinv Hgrd am Href) (y, am')
                 ∧ refine am' m'

instance {α} [Machine CTX M] [Machine ACTX AM] [Refinement AM M]
  (abs : OrdinaryNDEvent AM α' Unit) :
  Coe (OrdinaryRNDEvent' AM M abs α) (OrdinaryRNDEvent AM M abs α Unit) where
  coe ev := {
    guard := ev.guard
    effect := ev.effect
    safety := ev.safety
    feasibility := ev.feasibility
    lift_in := ev.lift_in
    lift_out := fun _ => ()
    strengthening := ev.strengthening
    simulation := ev.simulation
  }

@[simp]
def newREvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM α' Unit) (ev : OrdinaryRNDEvent' AM M abs α) :
  OrdinaryRNDEvent AM M abs α Unit := ev



structure OrdinaryRNDEvent'' (AM) [Machine ACTX AM] (M) [Machine CTX M]
  [instR : Refinement AM M] (abs : OrdinaryNDEvent AM Unit Unit)
  extends OrdinaryNDEvent M Unit Unit where

  strengthening (m : M) :
    Machine.invariant m
    → guard m ()
    → ∀ am, refine am m
      → abs.guard am ()

  simulation (m : M):
    (Hinv : Machine.invariant m)
    → (Hgrd : guard m ())
    → ∀ y, ∀ m', effect m x Hgrd (y, m')
      → ∀ am, (Href : refine am m)
        → ∃ am', abs.effect am () (strengthening m Hinv Hgrd am Href) (y, am')
                 ∧ refine am' m'

instance [Machine CTX M] [Machine ACTX AM] [Refinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit) :
  Coe (OrdinaryRNDEvent'' AM M abs) (OrdinaryRNDEvent AM M abs Unit Unit) where
  coe ev := {
    guard := ev.guard
    effect := ev.effect
    safety := ev.safety
    feasibility := ev.feasibility
    lift_out := fun _ => ()
    lift_in := fun _ => ()
    strengthening m _ := ev.strengthening m
    simulation m _ := ev.simulation m
  }

@[simp]
def newREvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM α' Unit) (ev : OrdinaryRNDEvent' AM M abs α) :
  OrdinaryRNDEvent AM M abs α Unit := ev



/-!
### Ordinary initialization events
-/

class SafeInitRNDEventPO  {α β α' β'} [Machine ACTX AM] [Machine CTX M]
  [instR: Refinement AM M]
  (ev : _InitNDEvent M α β) (abs : _InitNDEvent AM α' β') [instSafeEv : SafeInitNDEventPO ev]
  [instSafeAbs : SafeInitNDEventPO abs]
where
  lift_in : α → α'
  lift_out : β → β'

  strengthening (x : α) : ev.guard x → abs.guard (lift_in x)

  simulation (x : α):
    (Hgrd : ev.guard x)
    → ∀ y, ∀ m', ev.init x Hgrd (y, m')
        → ∃ am', abs.init (lift_in x) (strengthening x Hgrd) (lift_out y, am')
                 ∧ refine am' m'

structure SafeInitRNDEvent (AM) [Machine ACTX AM] (M) [Machine CTX M]
  [instR : Refinement AM M]
  {α' β'} (abs : InitNDEvent AM α' β') (α) (β) extends InitNDEvent  M α β where

  lift_in : α → α'
  lift_out : β → β'

  strengthening (x : α) : guard x → abs.guard (lift_in x)

  simulation (x : α):
    (Hgrd : guard x)
    → ∀ y, ∀ m', init x Hgrd (y, m')
        → ∃ am', abs.init (lift_in x) (strengthening x Hgrd) (lift_out y, am')
                 ∧ refine am' m'


instance [Machine ACTX AM] [Machine CTX M]
  [instR: Refinement AM M]
  (abs : InitNDEvent AM α' β') (ev : SafeInitRNDEvent AM M abs α β):
  SafeInitRNDEventPO
    (ev.to_InitNDEvent ) (abs.to_InitNDEvent )
    (instSafeAbs := safeInitNDEventPO_InitNDEvent abs)
    (instSafeEv := safeInitNDEventPO_InitNDEvent ev.toInitNDEvent)
  where
    lift_in := ev.lift_in
    lift_out := ev.lift_out
    strengthening := ev.strengthening
    simulation := ev.simulation

def newInitRNDEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : InitNDEvent AM α' β') (ev : SafeInitRNDEvent AM M abs α β) :
  SafeInitRNDEvent AM M abs α β := ev


structure SafeInitRNDEvent' (AM) [Machine ACTX AM] (M) [Machine CTX M]
  [instR: Refinement AM M]
  { α' } (abs : InitNDEvent AM α' Unit) (α)
  extends InitNDEvent' M α where
  /-- Transformation of output value: how a concrete output must be interpreted
  at the abstract level. -/
  lift_in: α → α'

  /-- Proof obligation: guard strengthening. -/
  strengthening (x : α ) : guard x → abs.guard (lift_in x)

  /-- Proof obligation: action simulation. -/
  simulation (x : α):
    (Hgrd : guard x)
    → ∀ y, ∀ m', init x Hgrd m'
        → ∃ am', abs.init (lift_in x) (strengthening x Hgrd) (y, am')
                 ∧ refine am' m'


instance {α} [Machine CTX M] [Machine ACTX AM] [Refinement AM M]
  (abs : InitNDEvent AM α' Unit) :
  Coe (SafeInitRNDEvent' AM M abs α) (SafeInitRNDEvent AM M abs α Unit) where
  coe ev := {
              lift_in := ev.lift_in
              lift_out := fun _ => ()
              strengthening := ev.strengthening
              simulation := ev.simulation
              guard := ev.guard
              init x grd m := ev.init x grd m.2
              safety x grd _ m := ev.safety x grd m
              feasibility x grd := ⟨(), ev.feasibility x grd⟩
            }


@[simp]
def newInitRNDEvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : InitNDEvent AM α' Unit) (ev : SafeInitRNDEvent' AM M abs α) :
  SafeInitRNDEvent AM M abs α Unit := ev


structure SafeInitRNDEvent'' (AM) [Machine ACTX AM] (M) [Machine CTX M]
  [instR: Refinement AM M] (abs : InitNDEvent AM Unit Unit)
  extends InitNDEvent'' M where
  /-- Proof obligation: guard strengthening. -/
  strengthening : guard → abs.guard ()

  /-- Proof obligation: action simulation. -/
  simulation :
    (Hgrd : guard)
    → ∀ y, ∀ m', init Hgrd m'
        → ∃ am', abs.init () (strengthening Hgrd) (y, am')
                 ∧ refine am' m'

instance [Machine CTX M] [Machine ACTX AM] [Refinement AM M]
  (abs : InitNDEvent AM Unit Unit) :
  Coe (SafeInitRNDEvent'' AM M abs) (SafeInitRNDEvent AM M abs Unit Unit ) where
  coe ev := {
              lift_in :=  fun _ => ()
              lift_out := fun _ => ()
              strengthening _ := ev.strengthening
              simulation _ := ev.simulation
              guard _ := ev.guard
              init _ grd m := ev.init grd m.2
              safety _ grd _ m := ev.safety grd m
              feasibility _ grd := ⟨(), ev.feasibility grd⟩
            }


@[simp]
def newInitREvent'' [Machine ACTX AM] [Machine CTX M]
  [Refinement AM M] (abs : InitNDEvent AM Unit Unit)
  (ev : SafeInitRNDEvent'' AM M abs ) : SafeInitRNDEvent AM M abs Unit Unit := ev
