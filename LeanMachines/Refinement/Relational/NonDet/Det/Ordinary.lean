
import LeanMachines.Refinement.Relational.Basic
import LeanMachines.NonDet.Ordinary
import LeanMachines.Refinement.Relational.NonDet.Det.Basic

#check  SafeRDetEventPO



open Refinement
/-!
# Deterministic refined Ordinary event from non-deterministic abstract events

-/

/-- The representation of ordinary deterministic refined events
with: `AM` the abstact machine type, `M` the concrete maching type,
 `α` the concrete input parameter type, `α'` the corresponding abstract input type (by default, `α`)
 `β` the concrete input parameter type, `β'` the corresponding abstract input type (by default, `β`)

Note that events, of type `OrdinaryRDetEvent`, are not directly constructed using this
structure. More user-friendly specification structures, such as `RDetEventSpec`, and smart constructors,
 such as `newRDetEvent` are preferably employed in practice.
 -/
structure OrdinaryRDetEvent (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  (α) (β) (α':=α) (β':=β) (abs : OrdinaryNDEvent AM α' β')
  extends OrdinaryEvent M α β where
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
    → ∀ am, (Href : refine am m)
      → let (y, m') := action m x Hgrd
        ∃ am', abs.effect am (lift_in x) (strengthening m x Hinv Hgrd am Href) (lift_out y, am')
               ∧ refine am' m'

instance [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (abs : OrdinaryNDEvent AM α' β') (ev : OrdinaryRDetEvent AM M α β α' β' abs):
  SafeRDetEventPO
    (ev.toEvent) (abs.toNDEvent)
    (instSafeAbs := instSafeNDEventPO_OrdinaryNDEvent abs)
    (instSafeEv := instSafeEventPO_OrdinaryEvent ev.toOrdinaryEvent)
    (valid_kind := by simp)
  where
    lift_in := ev.lift_in
    lift_out := ev.lift_out
    strengthening := ev.strengthening
    simulation := ev.simulation





/-!
  # Smart constructors
-/

def newRDetEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM α' β') (ev : OrdinaryRDetEvent AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) :
  OrdinaryRDetEvent AM M α β α' β' abs := ev


structure OrdinaryRDetEvent' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  { α' } (abs : OrdinaryNDEvent AM α' Unit) (α)
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
        ∃ am', abs.effect am (lift_in x) (strengthening m x Hinv Hgrd am Href) ((), am')
               ∧ refine am' m'

instance {α} [Machine CTX M] [Machine ACTX AM] [Refinement AM M] (abs : OrdinaryNDEvent AM α' Unit) :
  Coe (OrdinaryRDetEvent' AM M abs α) (OrdinaryRDetEvent AM M  α Unit α' Unit abs) where
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
def newRDetEvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (abs : OrdinaryNDEvent AM α' Unit)
  (ev : OrdinaryRDetEvent' AM M abs α) : OrdinaryRDetEvent AM M  α Unit α' Unit abs := ev



structure OrdinaryRDetEvent'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit)
  extends OrdinaryEvent'' M  where


  /-- Proof obligation: guard strengthening. -/
  strengthening (m : M)  :
    Machine.invariant m
    → guard m
    → ∀ am, refine am m
      → abs.guard am ()

  /-- Proof obligation: action simulation. -/
  simulation (m : M) (x : α):
    (Hinv : Machine.invariant m)
    → (Hgrd : guard m )
    → ∀ am, (Href : refine am m)
      → let m' := action m  Hgrd
        ∃ am', abs.effect am () (strengthening m Hinv Hgrd am Href) ((), am')
               ∧ refine am' m'

instance  [Machine CTX M] [Machine ACTX AM] [Refinement AM M] (abs : OrdinaryNDEvent AM Unit Unit) :
  Coe (OrdinaryRDetEvent'' AM M abs) (OrdinaryRDetEvent AM M  Unit Unit Unit Unit abs) where
  coe ev := {
              lift_in := fun _ => ()
              lift_out := fun _ => ()
              strengthening m _ := ev.strengthening m
              simulation :=
              fun m x hinv hgrd am href =>
                by
                  simp
                  exact ev.simulation m x hinv hgrd am href
              guard m _ := ev.guard m
              action m x grd := ((), ev.action m grd)
              safety m _ := ev.safety m
            }


@[simp]
def newRDetEvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (abs : OrdinaryNDEvent AM Unit Unit)
  (ev : OrdinaryRDetEvent'' AM M abs ) : OrdinaryRDetEvent AM M  Unit Unit Unit Unit abs := ev



/-!
### Ordinary initialization events
-/



class SafeInitRDetEventPO  {α β α' β'} [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : _InitEvent M α β) (abs : _InitNDEvent AM α' β') [instSafeAbs : SafeInitNDEventPO abs] [instSafeEv : SafeInitEventPO ev]
  where

  lift_in : α → α'
  lift_out : β → β'

  strengthening (x : α):
    ev.guard x
    → abs.guard (lift_in x)

  simulation (x : α):
    (Hgrd : ev.guard x)
    → let (y, m') := ev.init x Hgrd
      ∃ am', abs.init (lift_in x) (strengthening x Hgrd) (lift_out y, am')
             ∧ refine am' m'

structure InitRDetEvent (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  (α) (β) (α') (β') (abstract : InitNDEvent AM α' β')
  extends InitEvent M α β where

  lift_in : α → α'
  lift_out : β → β'

  strengthening (x : α):
    guard x
    → abstract.guard (lift_in x)

  simulation (x : α):
    (Hgrd : guard x)
    → let (y, m') := init x Hgrd
      ∃ am', abstract.init (lift_in x) (strengthening x Hgrd) (lift_out y, am')
              ∧ refine am' m'


instance [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (abs : InitNDEvent AM α' β') (ev : InitRDetEvent AM M α β α' β' abs):
  SafeInitRDetEventPO
    (ev.to_InitEvent) (abs.to_InitNDEvent)
    (instSafeAbs := safeInitNDEventPO_InitNDEvent abs)
    (instSafeEv := instSafeInitEventPO_InitEvent ev.toInitEvent)
  where
  lift_in := ev.lift_in
  lift_out := ev.lift_out
  strengthening := ev.strengthening
  simulation := ev.simulation


/-!
### Smart Constructors
-/

def newInitRDetEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : InitNDEvent AM α' β') (ev : InitRDetEvent AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : InitRDetEvent AM M α β α' β' abs :=
  ev



structure InitRDetEvent' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  { α' } (abs : InitNDEvent AM α' Unit) (α)
  extends InitEvent' M α where
  /-- Transformation of output value: how a concrete output must be interpreted
  at the abstract level. -/
  lift_in: α → α'

  /-- Proof obligation: guard strengthening. -/
  strengthening (x : α ) :
    guard x
      → abs.guard  (lift_in x)

  /-- Proof obligation: action simulation. -/
  simulation (x : α):
    (Hgrd : guard x)
      → let m' := init x Hgrd
        ∃ am', abs.init (lift_in x) (strengthening  x  Hgrd ) ((), am')
               ∧ refine am' m'

instance {α} [Machine CTX M] [Machine ACTX AM] [Refinement AM M] (abs : InitNDEvent AM α' Unit) :
  Coe (InitRDetEvent' AM M abs α) (InitRDetEvent AM M  α Unit α' Unit abs) where
  coe ev := {
              lift_in := ev.lift_in
              lift_out := fun _ => ()
              strengthening := ev.strengthening
              simulation :=
              fun  x  hgrd   =>
                by
                  simp
                  exact ev.simulation  x  hgrd
              guard := ev.guard
              init x grd := ((), ev.init x grd)
              safety := ev.safety
            }


@[simp]
def newInitRDetEvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (abs : InitNDEvent AM α' Unit)
  (ev : InitRDetEvent' AM M abs α) : InitRDetEvent AM M  α Unit α' Unit abs := ev



structure InitRDetEvent'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  (abs : InitNDEvent AM Unit Unit)
  extends InitEvent'' M  where


  strengthening:
    guard
    → abs.guard ()

  simulation:
    (Hgrd : guard)
    → let m' := init Hgrd
      ∃ am', abs.init () (strengthening Hgrd) ((), am')
              ∧ refine am' m'

instance  [Machine CTX M] [Machine ACTX AM] [Refinement AM M] (abs : InitNDEvent AM Unit Unit) :
  Coe (InitRDetEvent'' AM M abs) (InitRDetEvent AM M  Unit Unit Unit Unit abs) where
  coe ev := {
              lift_in := fun _ => ()
              lift_out := fun _ => ()
              strengthening _ := ev.strengthening
              simulation :=
              fun x  hgrd  =>
                by
                  simp
                  exact ev.simulation hgrd
              guard _ := ev.guard
              init x grd := ((), ev.init grd)
              safety _ grd := ev.safety grd
            }


@[simp]
def newInitRDetEvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (abs : InitNDEvent AM Unit Unit)
  (ev : InitRDetEvent'' AM M abs ) : InitRDetEvent AM M  Unit Unit Unit Unit abs := ev
