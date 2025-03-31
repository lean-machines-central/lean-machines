
import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary
import LeanMachines.Event.Convergent
/-!

# Relational refinement

This module contains the basic definitions of the relational
refinement principles for LeanMachines.

This is heavily inspired by the Event-B refinement principles
with some slight differences:

  - concrete events are not obligatory convergent (but may be, of course)
  - event merging is only indirectly supported
  - events can be composed in various ways, and machines do not directly
    integrate events.
  - alternative (and compatible) refinement principles may be (and are) proposed

-/

/-!

## Machine refinement

-/

/-- The typeclass definition for the functional refinement
of an abstract machine type `AM` (in context `ACTX`) by
 a (more) concrete machine type `M` (in context `CTX`).
-/

class Refinement {ACTX : outParam (Type u₁)} (AM)
                 [Machine ACTX AM]
                 {CTX : outParam (Type u₂)} (M)
                 [Machine CTX M] where

  /-- The relation between the abstract machine type `AM` and
   the concrete machine type `M`, defined as a type-theoretic proposition. -/
  refine : AM → M → Prop

  /-- The safety requirement of refinement. -/
  refine_safe (am : AM) (m : M):
    Machine.invariant m
    → refine am m
    → Machine.invariant am

open Refinement


/-!

## Event refinement

### Ordinary transitional events

-/


@[simp]
def EventKind.isConvergent? (k : EventKind) :=
  match k with
  | TransDet Convergence.Convergent => true
  | TransNonDet Convergence.Convergent => true
  | _ => false

@[simp]
def EventKind.isAnticipated? (k : EventKind) :=
  match k with
  | TransDet Convergence.Anticipated => true
  | TransNonDet Convergence.Anticipated => true
  | _ => false

@[simp]
def EventKind.isOrdinary? (k : EventKind) :=
  match k with
  | TransDet Convergence.Ordinary => true
  | TransNonDet Convergence.Ordinary => true
  | _ => false

/-k₁ is the concrete kind and k₂ the abstract one-/
@[simp]
def EventKind.canRefine? (k₁ k₂ : EventKind) : Bool :=
  if k₂.isConvergent? then k₁.isConvergent?
  else if k₂.isAnticipated? then (not k₁.isOrdinary?)
       else k₂.isOrdinary?
/-
  This typeclass specifies the proof obligations for the refinement of events.
-/


class SafeREventPO {α β α' β'} [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : Event M α β) (abs : Event AM α' β') [instSafeAbs : SafeEventPO abs kabs] [instSafeEv : SafeEventPO ev kev]
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
    → ∀ am, (Href: refine am m)
      → let (y, m') := ev.action m x Hgrd
        let (z, am') := abs.action am (lift_in x) (strengthening m x Hinv Hgrd am Href)
        lift_out y = z ∧ refine am' m'

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
@[simp]
def newREvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (abs : OrdinaryEvent AM α' β')
  (ev : OrdinaryREvent AM M abs (α := Unit) (β := β)) : OrdinaryREvent AM M abs (α := Unit) (β := β) := ev
@[simp]
def newREvent''[Machine ACTX AM] [Machine CTX M] [Refinement AM M] (abs : OrdinaryEvent AM α' β')
  (ev : OrdinaryREvent AM M abs (α := Unit) (β := Unit)) : OrdinaryREvent AM M abs (α := Unit) (β := Unit) := ev


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

@[simp]
def newAnticipatedREvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (abs : OrdinaryEvent AM α' β') [Preorder v]
  (ev: AnticipatedREvent AM M abs (α := Unit) (β := β) (v := v))
  : AnticipatedREvent AM M abs (α := Unit) (β := β) (v := v):= ev
@[simp]
def newAnticipatedREvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (abs : OrdinaryEvent AM α' β') [Preorder v]
  (ev: AnticipatedREvent AM M abs (α := Unit) (β := Unit) (v := v))
  : AnticipatedREvent AM M abs (α := Unit) (β := Unit) (v := v):= ev


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

@[simp]
def newConvergentREvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (abs : OrdinaryEvent AM α' β') [Preorder v] [WellFoundedLT v]
  (ev: ConvergentREvent AM M abs (α := Unit) (β := β) (v := v))
  : ConvergentREvent AM M abs (α := Unit) (β := β) (v := v):= ev
@[simp]
def newConvergentREvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (abs : OrdinaryEvent AM α' β') [Preorder v] [WellFoundedLT v]
  (ev: ConvergentREvent AM M abs (α := Unit) (β := Unit) (v := v))
  : ConvergentREvent AM M abs (α := Unit) (β := Unit) (v := v):= ev




/-!
### Ordinary initialization events
-/


/-
  We follow the same idea as for SafeInitEvent : the typeclass specifies the refinement of initialisation
  events and then allows a conversion to regular refined events
-/

class SafeInitREventPO  {α β α' β'} [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : _InitEvent M α β) (abs : _InitEvent AM α' β') [instSafeEv : SafeInitEventPO ev] [instSafeAbs : SafeInitEventPO abs]
where
  lift_in : α → α'
  lift_out : β → β'

  strengthening (x : α) : ev.guard x → abs.guard (lift_in x)

  simulation (x : α) :
    (Hgrd : ev.guard x) →
      let (y, m') := ev.init x Hgrd
      let (z, am') := abs.init (lift_in x) (strengthening x Hgrd)
      lift_out y = z ∧ refine am' m'

structure SafeInitREvent (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR : Refinement AM M]
  {α β α' β'} (abs : InitEvent AM α' β') extends InitEvent  M α β where
  lift_in : α → α'
  lift_out : β → β'

  strengthening (x : α) : guard x → abs.guard (lift_in x)

  simulation (x : α) :
    (Hgrd : guard x) →
      let (y, m') := init x Hgrd
      let (z, am') := abs.init (lift_in x) (strengthening x Hgrd)
      lift_out y = z ∧ refine am' m'


instance [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (abs : InitEvent AM α' β') (ev : SafeInitREvent AM M abs):
  SafeInitREventPO
    (AM := AM) (M := M)
    (α := α) (β := β)
    (ev.to_InitEvent (M := M)) (abs.to_InitEvent (M := AM))
    (instSafeAbs := safeInitEventPO_InitEvent abs)
    (instSafeEv := safeInitEventPO_InitEvent ev.toInitEvent)
  where
    lift_in := ev.lift_in
    lift_out := ev.lift_out
    strengthening := ev.strengthening
    simulation := ev.simulation


def newInitREvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : InitEvent AM α' β') (ev : SafeInitREvent AM M abs (α := α) (β := β)) : SafeInitREvent AM M abs (α := α) (β := β) := ev


def newInitREvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : InitEvent AM α' β') (ev : SafeInitREvent AM M abs (α := Unit) (β := β)) : SafeInitREvent AM M abs (α := Unit) (β := β) := ev

def newInitREvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : InitEvent AM α' β') (ev : SafeInitREvent AM M abs (α := Unit) (β := Unit)) : SafeInitREvent AM M abs (α := Unit) (β := Unit) := ev



-- class RefineDefault (AM) (M) [Machine ACTX AM] [Machine CTX M] [Inhabited AM] [Inhabited M]  [Refinement AM M] where
--   refine_default (am : AM) (m : M) : m = default → refine am m → am = default


-- instance [DecidableEq M] [DecidableEq AM] [Machine ACTX AM] [Machine CTX M] [instR : Refinement AM M]
--     [Inhabited AM] [Inhabited M] [instRDef : RefineDefault AM M]
--    (ev : _InitEvent M α β ) (abs : _InitEvent AM α' β') [SafeInitEventPO abs] [SafeInitEventPO ev]
--    [instSafeInitR : SafeInitREvent ev abs] :

--    SafeREventPO ev abs.toEvent (kev := EventKind.InitDet) (kabs := EventKind.InitDet)
--     (valid_kind :=
--       by
--         simp[EventKind.refine?]
--         simp[EventKind.get_status]
--       ) -- The proof is not automatic
-- where
--     lift_in := instSafeInitR.lift_in
--     lift_out := instSafeInitR.lift_out

--     strengthening m x :=
--       by
--         simp
--         intros hinv hdef hgrd am href
--         apply And.intro
--         case left =>
--           apply instRDef.refine_default am m hdef href
--         case right =>
--           exact SafeInitREvent.strengthening x hgrd
--     simulation m x hinv hgrd am href := SafeInitREvent.simulation x (InitEvent.toEvent.proof_1 ev m x hgrd)



-- # Double refinement



-- We add a structure + smart constructor for the specific case where a concrete event refines two abstract events

structure DoubleOrdinaryREvent
  {α β}
  (AM₁) [Machine ACTX₁ AM₁]
  (AM₂) [Machine ACTX₂ AM₂]
  (M) [Machine CTX M] [instR₁ : Refinement AM₁ M] [instR₂ : Refinement AM₂ M]
  (abs₁ : OrdinaryEvent AM₁ α'₁ β'₁)
  (abs₂ : OrdinaryEvent AM₂ α'₂ β'₂)
  extends OrdinaryEvent M α β
  where
    -- First refinement

    lift_in₁ : α → α'₁
    lift_out₁ : β → β'₁

    strengthening₁ (m : M) (x : α):
      Machine.invariant m
      → guard m x
      → ∀ am, refine am m
        → abs₁.guard am (lift_in₁ x)

    simulation₁ (m : M) (x : α):
      (Hinv : Machine.invariant m)
      → (Hgrd : guard m x)
      → ∀ am, (Href: refine am m)
        → let (y, m') := action m x Hgrd
          let (z, am') := abs₁.action am (lift_in₁ x) (strengthening₁ m x Hinv Hgrd am Href)
          lift_out₁ y = z ∧ (refine am' m')

    -- Second refinement

    lift_in₂ : α → α'₂
    lift_out₂ : β → β'₂

    strengthening₂ (m : M) (x : α):
      Machine.invariant m
      → guard m x
      → ∀ am, refine am m
        → abs₂.guard am (lift_in₂ x)

    simulation₂ (m : M) (x : α):
      (Hinv : Machine.invariant m)
      → (Hgrd : guard m x)
      → ∀ am, (Href: refine am m)
        → let (y, m') := action m x Hgrd
          let (z, am') := abs₂.action am (lift_in₂ x) (strengthening₂ m x Hinv Hgrd am Href)
          lift_out₂ y = z ∧ (refine am' m')


instance [Machine ACTX₁ AM₁] [Machine ACTX₂ AM₂] [Machine CTX M] [instR₁ : Refinement AM₁ M][instR₂ : Refinement AM₂ M]
  (abs₁ : OrdinaryEvent AM₁ α'₁ β'₁) (abs₂ : OrdinaryEvent AM₂ α'₂ β'₂)
  (ev : DoubleOrdinaryREvent AM₁ AM₂ M abs₁ abs₂ (instR₂ := instR₂) (instR₁ := instR₁)) :
  SafeREventPO
    (AM := AM₁) (M := M)
    (α := α) (β := β)
    (ev.toEvent (M := M)) (abs₁.toEvent (M := AM₁))
    (instSafeAbs := instSafeEventPO_OrdinaryEvent abs₁)
    (instSafeEv := instSafeEventPO_OrdinaryEvent ev.toOrdinaryEvent)
    (valid_kind := by simp)
  where
    lift_in := ev.lift_in₁
    lift_out := ev.lift_out₁
    strengthening := ev.strengthening₁
    simulation := ev.simulation₁


instance [Machine ACTX₁ AM₁] [Machine ACTX₂ AM₂] [Machine CTX M] [instR₁ : Refinement AM₁ M][instR₂ : Refinement AM₂ M]
  (abs₁ : OrdinaryEvent AM₁ α'₁ β'₁) (abs₂ : OrdinaryEvent AM₂ α'₂ β'₂)
  (ev : DoubleOrdinaryREvent AM₁ AM₂ M abs₁ abs₂ (instR₂ := instR₂) (instR₁ := instR₁)) :
  SafeREventPO
    (AM := AM₂) (M := M)
    (α := α) (β := β)
    (ev.toEvent (M := M)) (abs₂.toEvent (M := AM₂))
    (instSafeAbs := instSafeEventPO_OrdinaryEvent abs₂)
    (instSafeEv := instSafeEventPO_OrdinaryEvent ev.toOrdinaryEvent)
    (valid_kind := by simp)
  where
    lift_in := ev.lift_in₂
    lift_out := ev.lift_out₂
    strengthening := ev.strengthening₂
    simulation := ev.simulation₂

@[simp]
def newDoubleOrdinaryREvent [Machine ACTX₁ AM₁] [Machine ACTX₂ AM₂] [Machine CTX M] [Refinement AM₁ M] [Refinement AM₂ M]
  (abs₁ : OrdinaryEvent AM₁ α'₁ β'₁)
  (abs₂ : OrdinaryEvent AM₂ α'₂ β'₂)
  (ev: DoubleOrdinaryREvent AM₁ AM₂ M abs₁ abs₂ (α := α) (β := β))
  :  DoubleOrdinaryREvent AM₁ AM₂ M abs₁ abs₂ (α := α) (β := β) := ev
@[simp]
def newDoubleOrdinaryREvent' [Machine ACTX₁ AM₁] [Machine ACTX₂ AM₂] [Machine CTX M] [Refinement AM₁ M] [Refinement AM₂ M]
  (abs₁ : OrdinaryEvent AM₁ α'₁ β'₁)
  (abs₂ : OrdinaryEvent AM₂ α'₂ β'₂)
  (ev: DoubleOrdinaryREvent AM₁ AM₂ M abs₁ abs₂ (α := Unit) (β := β))
  :  DoubleOrdinaryREvent AM₁ AM₂ M abs₁ abs₂ (α := Unit) (β := β) := ev
@[simp]
def newDoubleOrdinaryREvent'' [Machine ACTX₁ AM₁] [Machine ACTX₂ AM₂] [Machine CTX M] [Refinement AM₁ M] [Refinement AM₂ M]
  (abs₁ : OrdinaryEvent AM₁ α'₁ β'₁)
  (abs₂ : OrdinaryEvent AM₂ α'₂ β'₂)
  (ev: DoubleOrdinaryREvent AM₁ AM₂ M abs₁ abs₂ (α := Unit) (β := Unit))
  :  DoubleOrdinaryREvent AM₁ AM₂ M abs₁ abs₂ (α := Unit) (β := Unit) := ev


-- ### Double refinement of init events



structure DoubleInitREvent
  {α β}
  (AM₁) [Machine ACTX₁ AM₁]
  (AM₂) [Machine ACTX₂ AM₂]
  (M) [Machine CTX M] [instR₁ : Refinement AM₁ M] [instR₂ : Refinement AM₂ M]
  (abs₁ : InitEvent AM₁ α'₁ β'₁)
  (abs₂ : InitEvent AM₂ α'₂ β'₂)
  extends InitEvent M α β
  where
    lift_in₁ : α → α'₁
    lift_out₁ : β → β'₁

    strengthening₁ (x : α) : guard x → abs₁.guard (lift_in₁ x)

    simulation₁ (x : α) :
      (Hgrd : guard x) →
        let (y, m') := init x Hgrd
        let (z, am') := abs₁.init (lift_in₁ x) (strengthening₁ x Hgrd)
        lift_out₁ y = z ∧ refine am' m'
    lift_in₂ : α → α'₂
    lift_out₂ : β → β'₂

    strengthening₂ (x : α) : guard x → abs₂.guard (lift_in₂ x)

    simulation₂ (x : α) :
      (Hgrd : guard x) →
        let (y, m') := init x Hgrd
        let (z, am') := abs₂.init (lift_in₂ x) (strengthening₂ x Hgrd)
        lift_out₂ y = z ∧ refine am' m'

instance [Machine ACTX₁ AM₁] [Machine ACTX₂ AM₂] [Machine CTX M] [instR₁ : Refinement AM₁ M][instR₂ : Refinement AM₂ M]
  (abs₁ : InitEvent AM₁ α'₁ β'₁) (abs₂ : InitEvent AM₂ α'₂ β'₂)
  (ev : DoubleInitREvent AM₁ AM₂ M abs₁ abs₂ (instR₂ := instR₂) (instR₁ := instR₁)) :
  SafeInitREventPO
    (AM := AM₁) (M := M)
    (α := α) (β := β)
    (ev.to_InitEvent (M := M)) (abs₁.to_InitEvent (M := AM₁))
    (instSafeAbs := safeInitEventPO_InitEvent abs₁)
    (instSafeEv := safeInitEventPO_InitEvent ev.toInitEvent)
  where
    lift_in := ev.lift_in₁
    lift_out := ev.lift_out₁
    strengthening := ev.strengthening₁
    simulation := ev.simulation₁


instance [Machine ACTX₁ AM₁] [Machine ACTX₂ AM₂] [Machine CTX M] [instR₁ : Refinement AM₁ M][instR₂ : Refinement AM₂ M]
  (abs₁ : InitEvent AM₁ α'₁ β'₁) (abs₂ : InitEvent AM₂ α'₂ β'₂)
  (ev : DoubleInitREvent AM₁ AM₂ M abs₁ abs₂ (instR₂ := instR₂) (instR₁ := instR₁)) :
  SafeInitREventPO
    (AM := AM₂) (M := M)
    (α := α) (β := β)
    (ev.to_InitEvent (M := M)) (abs₂.to_InitEvent (M := AM₂))
    (instSafeAbs := safeInitEventPO_InitEvent abs₂)
    (instSafeEv := safeInitEventPO_InitEvent ev.toInitEvent)
  where
    lift_in := ev.lift_in₂
    lift_out := ev.lift_out₂
    strengthening := ev.strengthening₂
    simulation := ev.simulation₂


def newDoubleInitREvent [Machine ACTX₁ AM₁] [Machine ACTX₂ AM₂] [Machine CTX M] [Refinement AM₁ M] [Refinement AM₂ M]
  (abs₁ : InitEvent AM₁ α'₁ β'₁)
  (abs₂ : InitEvent AM₂ α'₂ β'₂)
  (ev: DoubleInitREvent AM₁ AM₂ M abs₁ abs₂ (α := α) (β := β))
  :  DoubleInitREvent AM₁ AM₂ M abs₁ abs₂ (α := α) (β := β) := ev
@[simp]
def newDoubleInitREvent' [Machine ACTX₁ AM₁] [Machine ACTX₂ AM₂] [Machine CTX M] [Refinement AM₁ M] [Refinement AM₂ M]
  (abs₁ : InitEvent AM₁ α'₁ β'₁)
  (abs₂ : InitEvent AM₂ α'₂ β'₂)
  (ev: DoubleInitREvent AM₁ AM₂ M abs₁ abs₂ (α := Unit) (β := β))
  :  DoubleInitREvent AM₁ AM₂ M abs₁ abs₂ (α := Unit) (β := β) := ev
@[simp]
def newDoubleInitREvent'' [Machine ACTX₁ AM₁] [Machine ACTX₂ AM₂] [Machine CTX M] [Refinement AM₁ M] [Refinement AM₂ M]
  (abs₁ : InitEvent AM₁ α'₁ β'₁)
  (abs₂ : InitEvent AM₂ α'₂ β'₂)
  (ev: DoubleInitREvent AM₁ AM₂ M abs₁ abs₂ (α := Unit) (β := Unit))
  :  DoubleInitREvent AM₁ AM₂ M abs₁ abs₂ (α := Unit) (β := Unit) := ev
