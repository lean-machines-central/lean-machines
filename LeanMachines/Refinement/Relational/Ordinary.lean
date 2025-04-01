import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary
import LeanMachines.Event.Convergent
import LeanMachines.Refinement.Relational.Basic

open Refinement


/-- Specification of ordinary refined events.
with: `AM` the abstact machine type, `M` the concrete maching type,
 `α` the concrete input parameter type, `α'` the corresponding abstract input type (by default, `α`)
 `β` the concrete input parameter type, `β'` the corresponding abstract input type (by default, `β`)
The `abs` parameter is the ordinary event intended to be refined.

Note that `abs` should not be anticipated nor convergent.

The input and output types can be lifted to the abstract, if needed,
 using the `lift_in` and `lift_out` components.

The proof obligations, beyond `safety` (of abstract events) are guard `strengthening`
and abstract event `simulation`.
 -/
structure OrdinaryREvent (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  {α β α' β'} (abs : OrdinaryEvent AM α' β')
  extends OrdinaryEvent M α β where

  /-- Transformation of input parameters: how a concrete parameter must be interpreted
  at the abstract level. -/
  lift_in : α → α'

  /-- Transformation of output value: how a concrete output must be interpreted
  at the abstract level. -/
  lift_out : β → β'

  /-- Proof obligation: guard strengthening. -/
  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ am, refine am m
      → abs.guard am (lift_in x)

  /-- Proof obligation: action simulation. -/
  simulation (m : M) (x : α):
    (Hinv : Machine.invariant m)
    → (Hgrd : guard m x)
    → ∀ am, (Href : refine am m)
      → let (y, m') := action m x Hgrd
        let (z, am') := abs.action am (lift_in x) (strengthening m x Hinv Hgrd am Href)
        lift_out y = z ∧ refine am' m'

#check SafeREventPO

instance [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (abs : OrdinaryEvent AM α' β') (ev : OrdinaryREvent AM M abs):
  SafeREventPO
    (AM := AM) (M := M)
    (α := α) (β := β)
    (ev.toEvent (M := M)) (abs.toEvent (M := AM))
    (instSafeAbs := instSafeEventPO_OrdinaryEvent abs)
    (instSafeEv := instSafeEventPO_OrdinaryEvent ev.toOrdinaryEvent)
    (valid_kind := by simp)
  where
    lift_in := ev.lift_in
    lift_out := ev.lift_out
    strengthening := ev.strengthening
    simulation := ev.simulation

/-- Smart constructor for ordinary refined event (and its alternative versions with Unit as input/output types),
with: `abs` the (ordinary) event to refine, and
  `ev` the refined event specification (cf. `REventSpec`).
-/
@[simp]
def newREvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (abs : OrdinaryEvent AM α' β')
  (ev: OrdinaryREvent AM M abs (α := α) (β := β))
  : OrdinaryREvent AM M abs (α := α) (β := β) := ev

structure OrdinaryREvent' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  { α α' } (abs : OrdinaryEvent' AM α')
  extends OrdinaryEvent' M α where
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
    → ∀ am, (Href : refine am m)
      → let m' := action m x Hgrd
        let am' := abs.action am (lift_in x) (strengthening m x Hinv Hgrd am Href)
        refine am' m'

instance {α} [Machine CTX M] [Machine ACTX AM] [Refinement AM M] (abs : OrdinaryEvent' AM α') :
  Coe (OrdinaryREvent' (α := α) AM M abs) (OrdinaryREvent AM M (α := α) (β := Unit) (Ord'.coe abs) ) where
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
            }


@[simp]
def newREvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (abs : OrdinaryEvent' AM α')
  (ev : OrdinaryREvent' AM M abs (α := α)) : OrdinaryREvent' AM M abs (α := α) := ev


structure OrdinaryREvent'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  (abs : OrdinaryEvent'' AM )
  extends OrdinaryEvent'' M  where

  /-- Proof obligation: guard strengthening. -/
  strengthening (m : M) :
    Machine.invariant m
    → guard m
    → ∀ am, refine am m
      → abs.guard am

  /-- Proof obligation: action simulation. -/
  simulation (m : M) :
    (Hinv : Machine.invariant m)
    → (Hgrd : guard m)
    → ∀ am, (Href : refine am m)
      → let m' := action m Hgrd
        let am':= abs.action am (strengthening m Hinv Hgrd am Href)
        refine am' m'

instance {α} [Machine CTX M] [Machine ACTX AM] [Refinement AM M] (abs : OrdinaryEvent'' AM):
  Coe (OrdinaryREvent'' AM M abs) (OrdinaryREvent AM M (α := α) (β := Unit) (Ord''.coe abs) ) where
  coe ev := {
              lift_in := fun _ => ()
              lift_out := fun _ => ()
              strengthening m _ := ev.strengthening m
              simulation :=
              fun m x hinv hgrd am href =>
                by
                  simp
                  exact ev.simulation m hinv hgrd am href
              guard m := fun _ => ev.guard m
              action m x grd := ((), ev.action m grd)
              safety m _ := ev.safety m
            }
@[simp]
def newREvent''[Machine ACTX AM] [Machine CTX M] [Refinement AM M] (abs : OrdinaryEvent'' AM )
  (ev : OrdinaryREvent'' AM M abs) : OrdinaryREvent'' AM M abs:= ev
