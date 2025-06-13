
import LeanMachines.NonDet.Basic
import LeanMachines.NonDet.Ordinary
import LeanMachines.Refinement.Relational.Basic
import LeanMachines.Refinement.Relational.NonDet.Basic



open Refinement
/-!
# Refinement of Ordinary non-deterministic event from non-deterministic abstract events

-/


structure OrdinaryRNDEvent (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  (α) (β) (α':=α) (β':=β) (abs : OrdinaryNDEvent AM α' β')
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
  (abs : OrdinaryNDEvent AM α' β') (ev : OrdinaryRNDEvent AM M α β α' β' abs):
  SafeRNDEventPO
    (ev.toNDEvent) (abs.toNDEvent)
    (instSafeAbs := instSafeNDEventPO_Ordinary abs)
    (instSafeEv := instSafeNDEventPO_Ordinary ev.toOrdinaryNDEvent)
    (valid_kind := by simp)
  where
    lift_in := ev.lift_in
    lift_out := ev.lift_out
    strengthening := ev.strengthening
    simulation := ev.simulation





/-!
  # Smart constructors
-/

def newRNDEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM α' β') (ev : OrdinaryRNDEvent AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) :
  OrdinaryRNDEvent AM M α β α' β' abs := ev


structure OrdinaryRNDEvent' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  { α' } (abs : OrdinaryNDEvent AM α' Unit) (α)
  extends OrdinaryNDEvent' M α where
  /-- Transformation of output value: how a concrete output must be interpreted
  at the abstract level. -/
  lift_in: α → α'

  /-- Proof obligation: guard strengthening. -/
  strengthening (m : M) (x : α ) :
    Machine.invariant m
    → guard m x
    → ∀ am, refine am m
      → abs.guard am (lift_in x)

  /-- Proof obligation: action simulation. -/
  simulation (m : M) (x : α):
    (Hinv : Machine.invariant m)
    → (Hgrd : guard m x)
    → ∀ m', effect m x Hgrd m'
      -- XXX : some constraint on output ?
      → ∀ am, (Href : refine am m)
        → ∃ am', abs.effect am (lift_in x) (strengthening m x Hinv Hgrd am Href) ((), am')
                 ∧ refine am' m'
#check Exists.intro
instance {α} [Machine CTX M] [Machine ACTX AM] [Refinement AM M] (abs : OrdinaryNDEvent AM α' Unit) :
  Coe (OrdinaryRNDEvent' AM M abs α) (OrdinaryRNDEvent AM M  α Unit α' Unit abs) where
  coe ev := {
              lift_in := ev.lift_in
              lift_out := fun _ => ()
              strengthening := ev.strengthening
              simulation m x hinv grd _ m' := ev.simulation m x hinv grd m'
              guard := ev.guard
              effect m x grd ym' := ev.effect m x grd ym'.2
              safety m x hinv hgrd _ m' := ev.safety m x hinv hgrd m'
              feasibility m x hinv grd := ⟨(), ev.feasibility m x hinv grd⟩
            }



@[simp]
def newRNDEvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (abs : OrdinaryNDEvent AM α' Unit)
  (ev : OrdinaryRNDEvent' AM M abs α) : OrdinaryRNDEvent AM M  α Unit α' Unit abs := ev



structure OrdinaryRNDEvent'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit)
  extends OrdinaryNDEvent'' M  where


  strengthening (m : M):
    Machine.invariant m
    → guard m
    → ∀ am, refine am m
      → abs.guard am ()

  simulation (m : M):
    (Hinv : Machine.invariant m)
    → (Hgrd : guard m)
    → ∀ m', effect m Hgrd m'
      → ∀ am, (Href : refine am m)
        → ∃ am', abs.effect am () (strengthening m Hinv Hgrd am Href) ((), am')
                 ∧ refine am' m'

instance  [Machine CTX M] [Machine ACTX AM] [Refinement AM M] (abs : OrdinaryNDEvent AM Unit Unit) :
  Coe (OrdinaryRNDEvent'' AM M abs) (OrdinaryRNDEvent AM M  Unit Unit Unit Unit abs) where
  coe ev := {
              lift_in := fun _ => ()
              lift_out := fun _ => ()
              strengthening m _ := ev.strengthening m
              simulation m _ hinv grd _ m' := ev.simulation m hinv grd m'
              guard m _ := ev.guard m
              effect m _ grd ym' := ev.effect m grd ym'.2
              safety m _ hinv hgrd _ m' := ev.safety m hinv hgrd m'
              feasibility m _ hinv grd := ⟨(), ev.feasibility m hinv grd⟩
            }


@[simp]
def newRNDEvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (abs : OrdinaryNDEvent AM Unit Unit)
  (ev : OrdinaryRNDEvent'' AM M abs ) : OrdinaryRNDEvent AM M  Unit Unit Unit Unit abs := ev



/-!
### Ordinary initialization events
-/



class SafeInitRNDEventPO  {α β α' β'} [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : _InitNDEvent M α β) (abs : _InitNDEvent AM α' β')
  [instSafeAbs : SafeInitNDEventPO abs] [instSafeEv : SafeInitNDEventPO ev]
  where

  lift_in : α → α'
  lift_out : β → β'

  strengthening (x : α):
    ev.guard x
    → abs.guard (lift_in x)

  simulation (x : α):
    (Hgrd : ev.guard x)
    → ∀ y, ∀ m', ev.init x Hgrd (y, m')
      → ∃ am', abs.init (lift_in x) (strengthening x Hgrd) (lift_out y, am')
               ∧ refine am' m'

structure InitRNDEvent (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  (α) (β) (α') (β') (abstract : InitNDEvent AM α' β')
  extends InitNDEvent M α β where

  lift_in : α → α'
  lift_out : β → β'

  strengthening (x : α):
    guard x
    → abstract.guard (lift_in x)

  simulation (x : α):
    (Hgrd : guard x)
    → ∀ y, ∀ m', init x Hgrd (y, m')
      → ∃ am', abstract.init (lift_in x) (strengthening x Hgrd) (lift_out y, am')
               ∧ refine am' m'


instance [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (abs : InitNDEvent AM α' β') (ev : InitRNDEvent AM M α β α' β' abs):
  SafeInitRNDEventPO
    (ev.to_InitNDEvent) (abs.to_InitNDEvent)
    (instSafeAbs := safeInitNDEventPO_InitNDEvent abs)
    (instSafeEv := safeInitNDEventPO_InitNDEvent ev.toInitNDEvent)
  where
  lift_in := ev.lift_in
  lift_out := ev.lift_out
  strengthening := ev.strengthening
  simulation := ev.simulation


/-!
### Smart Constructors
-/

def newInitRNDEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : InitNDEvent AM α' β') (ev : InitRNDEvent AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : InitRNDEvent AM M α β α' β' abs :=
  ev


structure InitRNDEvent' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  { α' } (abs : InitNDEvent AM α' Unit) (α)
  extends InitNDEvent' M α where
  /-- Transformation of output value: how a concrete output must be interpreted
  at the abstract level. -/
  lift_in: α → α'

  strengthening (x : α):
    guard x
    → abs.guard (lift_in x)

  simulation (x : α):
    (Hgrd : guard x)
    → ∀ m', init x Hgrd m'
      → ∃ am', abs.init (lift_in x) (strengthening x Hgrd) ((), am')
               ∧ refine am' m'

instance {α} [Machine CTX M] [Machine ACTX AM] [Refinement AM M] (abs : InitNDEvent AM α' Unit) :
  Coe (InitRNDEvent' AM M abs α) (InitRNDEvent AM M  α Unit α' Unit abs) where
  coe ev := {
              lift_in := ev.lift_in
              lift_out := fun _ => ()
              strengthening := ev.strengthening
              simulation x grd _ m' := ev.simulation x grd m'
              guard := ev.guard
              init x grd ym' := ev.init x grd ym'.2
              safety x  hgrd _ m' := ev.safety x hgrd m'
              feasibility x grd := ⟨(), ev.feasibility x grd⟩
            }


@[simp]
def newInitRNDEvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (abs : InitNDEvent AM α' Unit)
  (ev : InitRNDEvent' AM M abs α) : InitRNDEvent AM M  α Unit α' Unit abs := ev



structure InitRNDEvent'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  (abs : InitNDEvent AM Unit Unit)
  extends InitNDEvent'' M  where


  strengthening:
    guard
    → abs.guard ()

  simulation:
    (Hgrd : guard)
    → ∀ m', init Hgrd m'
      → ∃ am', abs.init () (strengthening Hgrd) ((), am')
               ∧ refine am' m'


instance  [Machine CTX M] [Machine ACTX AM] [Refinement AM M] (abs : InitNDEvent AM Unit Unit) :
  Coe (InitRNDEvent'' AM M abs) (InitRNDEvent AM M  Unit Unit Unit Unit abs) where
  coe ev := {
              lift_in := fun _ => ()
              lift_out := fun _ => ()
              strengthening _ := ev.strengthening
              simulation _ grd _ m' := ev.simulation grd m'
              guard _ := ev.guard
              init _ grd ym' := ev.init grd ym'.2
              safety _  hgrd _ m' := ev.safety hgrd m'
              feasibility _ grd := ⟨(), ev.feasibility grd⟩
            }


@[simp]
def newInitRNDEvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (abs : InitNDEvent AM Unit Unit)
  (ev : InitRNDEvent'' AM M abs ) : InitRNDEvent AM M  Unit Unit Unit Unit abs := ev
