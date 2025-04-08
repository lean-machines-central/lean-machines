import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary
import LeanMachines.Event.Convergent
import LeanMachines.Refinement.Relational.Basic
import LeanMachines.Refinement.Relational.Ordinary
import LeanMachines.Refinement.Relational.Convergent


open Refinement



-- # Double refinement



-- We add a structure + smart constructor for the specific case where a concrete event refines two abstract events

structure MultiOrdinaryREvent
  {α β}
  (AM₁) [Machine ACTX₁ AM₁]
  (AM₂) [Machine ACTX₂ AM₂]
  (M) [Machine CTX M] [instR₁ : Refinement AM₁ M] [instR₂ : Refinement AM₂ M]
  (abs₁ : OrdinaryEvent AM₁ α'₁ β'₁)
  (abs₂ : OrdinaryEvent AM₂ α'₂ β'₂)
  extends OrdinaryEvent M α β
  where
    ref₁ : OrdinaryREvent AM₁ M abs₁ {
        guard
        action
        safety
      }
    ref₂ : OrdinaryREvent AM₂ M abs₂ {
        guard
        action
        safety
      }


instance
  {ACTX₁ AM₁ ACTX₂ AM₂ CTX M}
  {α'₁ α β'₁ β α'₂ β'₂}
  [Machine ACTX₁ AM₁]
  [Machine ACTX₂ AM₂]
  (abs₁ : OrdinaryEvent AM₁ α'₁ β'₁)
  (abs₂ : OrdinaryEvent AM₂ α'₂ β'₂)
  [iCcr : Machine CTX M]
  [instR₁ : Refinement AM₁ M]  [instR₂ : Refinement AM₂ M]
  (rf : MultiOrdinaryREvent AM₁ AM₂ M abs₁ abs₂) :
  SafeREventPO
    (AM := AM₁) (M := M)
    (ACTX := ACTX₁) (CTX := CTX)
    (α := α) (β := β)
    (rf.toEvent) (abs₁.toEvent (M := AM₁))
    (instSafeAbs := instSafeEventPO_OrdinaryEvent abs₁)
    (instSafeEv := instSafeEventPO_OrdinaryEvent (rf.toOrdinaryEvent) )
    (valid_kind := by simp)
  where
    lift_in := rf.ref₁.lift_in
    lift_out := rf.ref₁.lift_out
    strengthening := rf.ref₁.strengthening
    simulation := rf.ref₁.simulation


instance [Machine ACTX₁ AM₁] [Machine ACTX₂ AM₂] [Machine CTX M] [instR₁ : Refinement AM₁ M][instR₂ : Refinement AM₂ M]
  (abs₁ : OrdinaryEvent AM₁ α'₁ β'₁) (abs₂ : OrdinaryEvent AM₂ α'₂ β'₂)
  (ev : MultiOrdinaryREvent AM₁ AM₂ M abs₁ abs₂ (instR₂ := instR₂) (instR₁ := instR₁)) :
  SafeREventPO
    (AM := AM₂) (M := M)
    (α := α) (β := β)
    (ev.toEvent (M := M)) (abs₂.toEvent (M := AM₂))
    (instSafeAbs := instSafeEventPO_OrdinaryEvent abs₂)
    (instSafeEv := instSafeEventPO_OrdinaryEvent ev.toOrdinaryEvent)
    (valid_kind := by simp)
  where
    lift_in := ev.ref₂.lift_in
    lift_out := ev.ref₂.lift_out
    strengthening := ev.ref₂.strengthening
    simulation := ev.ref₂.simulation

@[simp]
def newDoubleOrdinaryREvent [Machine ACTX₁ AM₁] [Machine ACTX₂ AM₂] [Machine CTX M] [Refinement AM₁ M] [Refinement AM₂ M]
  (abs₁ : OrdinaryEvent AM₁ α'₁ β'₁)
  (abs₂ : OrdinaryEvent AM₂ α'₂ β'₂)
  (ev: MultiOrdinaryREvent AM₁ AM₂ M abs₁ abs₂ (α := α) (β := β))
  :  MultiOrdinaryREvent AM₁ AM₂ M abs₁ abs₂ (α := α) (β := β) := ev


/-Smart constructors for when the output has type unit -/

structure DoubleOrdinaryREvent'
  {α}
  (AM₁) [Machine ACTX₁ AM₁]
  (AM₂) [Machine ACTX₂ AM₂]
  (M) [Machine CTX M] [instR₁ : Refinement AM₁ M] [instR₂ : Refinement AM₂ M]
  (abs₁ : OrdinaryEvent AM₁ α'₁ Unit)
  (abs₂ : OrdinaryEvent AM₂ α'₂ Unit)
  extends OrdinaryEvent' M α
  where
    -- First refinement

    lift_in₁ : α → α'₁

    strengthening₁ (m : M) (x : α):
      Machine.invariant m
      → guard m x
      → ∀ am, refine am m
        → abs₁.guard am (lift_in₁ x)

    simulation₁ (m : M) (x : α):
      (Hinv : Machine.invariant m)
      → (Hgrd : guard m x)
      → ∀ am, (Href: refine am m)
        → let m':= action m x Hgrd
          let (_,am') := abs₁.action am (lift_in₁ x) (strengthening₁ m x Hinv Hgrd am Href)
         (refine am' m')

    -- Second refinement

    lift_in₂ : α → α'₂

    strengthening₂ (m : M) (x : α):
      Machine.invariant m
      → guard m x
      → ∀ am, refine am m
        → abs₂.guard am (lift_in₂ x)

    simulation₂ (m : M) (x : α):
      (Hinv : Machine.invariant m)
      → (Hgrd : guard m x)
      → ∀ am, (Href: refine am m)
        → let m' := action m x Hgrd
          let (_,am') := abs₂.action am (lift_in₂ x) (strengthening₂ m x Hinv Hgrd am Href)
          (refine am' m')


-- instance {α} [Machine CTX M] [Machine ACTX₁ AM₁] [Refinement AM₁ M] [Machine ACTX₂ AM₂] [Refinement AM₂ M]
--   (abs₁ : OrdinaryEvent AM₁ α'₁ Unit) (abs₂ : OrdinaryEvent AM₂ α'₂ Unit):
--   Coe (DoubleOrdinaryREvent' (α := α) AM₁ AM₂ M abs₁ abs₂) (DoubleOrdinaryREvent AM₁ AM₂ M (α := α) (β := Unit) abs₁ abs₂) where
--   coe ev := {
--               lift_in₁ := ev.lift_in₁
--               lift_in₂ := ev.lift_in₂
--               lift_out₁ := fun _ => ()
--               lift_out₂ := fun _ => ()
--               strengthening₁ := ev.strengthening₁
--               strengthening₂ := ev.strengthening₂
--               simulation₁ :=
--               fun m x hinv hgrd am href =>
--                 by
--                   simp
--                   exact ev.simulation₁ m x hinv hgrd am href
--               simulation₂ :=
--               fun m x hinv hgrd am href =>
--                 by
--                   simp
--                   exact ev.simulation₂ m x hinv hgrd am href
--               guard := ev.guard
--               action m x grd := ((), ev.action m x grd)
--               safety := ev.safety
--             }

-- @[simp]
-- def newDoubleOrdinaryREvent' [Machine ACTX₁ AM₁] [Machine ACTX₂ AM₂] [Machine CTX M] [Refinement AM₁ M] [Refinement AM₂ M]
--   (abs₁ : OrdinaryEvent AM₁ α'₁ Unit )
--   (abs₂ : OrdinaryEvent AM₂ α'₂ Unit )
--   (ev: DoubleOrdinaryREvent' AM₁ AM₂ M abs₁ abs₂ (α := α ))
--   :  DoubleOrdinaryREvent AM₁ AM₂ M abs₁ abs₂ (α := α ) (β := Unit) := ev


/- Smart constructor when both the input and the output are of type Unit -/



structure DoubleOrdinaryREvent''
  (AM₁) [Machine ACTX₁ AM₁]
  (AM₂) [Machine ACTX₂ AM₂]
  (M) [Machine CTX M] [instR₁ : Refinement AM₁ M] [instR₂ : Refinement AM₂ M]
  (abs₁ : OrdinaryEvent AM₁ Unit Unit )
  (abs₂ : OrdinaryEvent AM₂ Unit Unit )
  extends OrdinaryEvent'' M
  where
    -- First refinement


    strengthening₁ (m : M):
      Machine.invariant m
      → guard m
      → ∀ am, refine am m
        → abs₁.guard am ()

    simulation₁ (m : M):
      (Hinv : Machine.invariant m)
      → (Hgrd : guard m )
      → ∀ am, (Href: refine am m)
        → let m':= action m Hgrd
          let (_,am') := abs₁.action am () (strengthening₁ m Hinv Hgrd am Href)
         (refine am' m')

    -- Second refinement


    strengthening₂ (m : M) :
      Machine.invariant m
      → guard m
      → ∀ am, refine am m
        → abs₂.guard am ()

    simulation₂ (m : M) :
      (Hinv : Machine.invariant m)
      → (Hgrd : guard m )
      → ∀ am, (Href: refine am m)
        → let m' := action m  Hgrd
          let (_,am') := abs₂.action am () (strengthening₂ m  Hinv Hgrd am Href)
          (refine am' m')


-- instance [Machine CTX M] [Machine ACTX₁ AM₁] [Refinement AM₁ M] [Machine ACTX₂ AM₂] [Refinement AM₂ M]
--   (abs₁ : OrdinaryEvent AM₁ Unit Unit) (abs₂ : OrdinaryEvent AM₂ Unit Unit):
--   Coe (DoubleOrdinaryREvent'' AM₁ AM₂ M abs₁ abs₂) (DoubleOrdinaryREvent AM₁ AM₂ M (α := Unit) (β := Unit) abs₁ abs₂) where
--   coe ev := {
--               lift_in₁ := fun _ => ()
--               lift_in₂ := fun _ => ()
--               lift_out₁ := fun _ => ()
--               lift_out₂ := fun _ => ()
--               strengthening₁ m x := ev.strengthening₁ m
--               strengthening₂ m x := ev.strengthening₂ m
--               simulation₁ :=
--               fun m x hinv hgrd am href =>
--                 by
--                   simp
--                   exact ev.simulation₁ m hinv hgrd am href
--               simulation₂ :=
--               fun m x hinv hgrd am href =>
--                 by
--                   simp
--                   exact ev.simulation₂ m hinv hgrd am href
--               guard m x := ev.guard m
--               action m x grd := ((), ev.action m grd)
--               safety m x := ev.safety m
--             }

-- @[simp]
-- def newDoubleOrdinaryREvent'' [Machine ACTX₁ AM₁] [Machine ACTX₂ AM₂] [Machine CTX M] [Refinement AM₁ M] [Refinement AM₂ M]
--   (abs₁ : OrdinaryEvent AM₁ Unit Unit)
--   (abs₂ : OrdinaryEvent AM₂ Unit Unit)
--   (ev: DoubleOrdinaryREvent'' AM₁ AM₂ M abs₁ abs₂ )
--   :  DoubleOrdinaryREvent AM₁ AM₂ M abs₁ abs₂ (α := Unit) (β := Unit) := ev


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
    ref₁ : SafeInitREvent AM₁ M abs₁ {init,safety}
    ref₂ : SafeInitREvent AM₂ M abs₂ {init,safety}

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
    lift_in := ev.ref₁.lift_in
    lift_out := ev.ref₁.lift_out
    strengthening := ev.ref₁.strengthening
    simulation := ev.ref₁.simulation


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
    lift_in := ev.ref₂.lift_in
    lift_out := ev.ref₂.lift_out
    strengthening := ev.ref₂.strengthening
    simulation := ev.ref₂.simulation


def newDoubleInitREvent [Machine ACTX₁ AM₁] [Machine ACTX₂ AM₂] [Machine CTX M] [Refinement AM₁ M] [Refinement AM₂ M]
  (abs₁ : InitEvent AM₁ α'₁ β'₁)
  (abs₂ : InitEvent AM₂ α'₂ β'₂)
  (ev: DoubleInitREvent AM₁ AM₂ M abs₁ abs₂ (α := α) (β := β))
  :  DoubleInitREvent AM₁ AM₂ M abs₁ abs₂ (α := α) (β := β) := ev


/- Smart constructor for when the init has Unit as output type -/


structure DoubleInitREvent'
  {α}
  (AM₁) [Machine ACTX₁ AM₁]
  (AM₂) [Machine ACTX₂ AM₂]
  (M) [Machine CTX M] [instR₁ : Refinement AM₁ M] [instR₂ : Refinement AM₂ M]
  (abs₁ : InitEvent AM₁ α'₁ Unit)
  (abs₂ : InitEvent AM₂ α'₂ Unit)
  extends InitEvent' M α
  where
    lift_in₁ : α → α'₁

    strengthening₁ (x : α) : guard x → abs₁.guard (lift_in₁ x)

    simulation₁ (x : α) :
      (Hgrd : guard x) →
        let m' := init x Hgrd
        let (_,am') := abs₁.init (lift_in₁ x) (strengthening₁ x Hgrd)
        refine am' m'

    lift_in₂ : α → α'₂

    strengthening₂ (x : α) : guard x → abs₂.guard (lift_in₂ x)

    simulation₂ (x : α) :
      (Hgrd : guard x) →
        let m' := init x Hgrd
        let (_,am') := abs₂.init (lift_in₂ x) (strengthening₂ x Hgrd)
        refine am' m'

-- instance {α} [Machine CTX M] [Machine ACTX₁ AM₁] [Refinement AM₁ M] [Machine ACTX₂ AM₂] [Refinement AM₂ M]
--   (abs₁ : InitEvent AM₁ α'₁ Unit) (abs₂ : InitEvent AM₂ α'₂ Unit):
--   Coe (DoubleInitREvent' (α := α) AM₁ AM₂ M abs₁ abs₂) (DoubleInitREvent AM₁ AM₂ M (α := α) (β := Unit) abs₁ abs₂) where
--   coe ev := {
--               lift_in₁ := ev.lift_in₁
--               lift_in₂ := ev.lift_in₂
--               lift_out₁ := fun _ => ()
--               lift_out₂ := fun _ => ()
--               strengthening₁ := ev.strengthening₁
--               strengthening₂ := ev.strengthening₂
--               simulation₁ :=
--               fun x hgrd =>
--                 by
--                   simp
--                   exact ev.simulation₁ x hgrd
--               simulation₂ :=
--               fun x hgrd  =>
--                 by
--                   simp
--                   exact ev.simulation₂ x hgrd
--               guard := ev.guard
--               init x grd := ((), ev.init x grd)
--               safety := ev.safety
--             }

-- @[simp]
-- def newDoubleInitREvent' [Machine ACTX₁ AM₁] [Machine ACTX₂ AM₂] [Machine CTX M] [Refinement AM₁ M] [Refinement AM₂ M]
--   (abs₁ : InitEvent AM₁ α'₁ Unit )
--   (abs₂ : InitEvent AM₂ α'₂ Unit )
--   (ev: DoubleInitREvent' AM₁ AM₂ M abs₁ abs₂ (α := α) )
--   :  DoubleInitREvent AM₁ AM₂ M abs₁ abs₂ (α := α ) (β := Unit) := ev


structure DoubleInitREvent''
  (AM₁) [Machine ACTX₁ AM₁]
  (AM₂) [Machine ACTX₂ AM₂]
  (M) [Machine CTX M] [instR₁ : Refinement AM₁ M] [instR₂ : Refinement AM₂ M]
  (abs₁ : InitEvent AM₁ Unit Unit)
  (abs₂ : InitEvent AM₂ Unit Unit)
  extends InitEvent'' M
  where
    strengthening₁ : guard → abs₁.guard ()

    simulation₁ :
      (Hgrd : guard ) →
        let m' := init Hgrd
        let (_,am'):= abs₁.init () (strengthening₁ Hgrd)
        refine am' m'

    strengthening₂  : guard → abs₂.guard ()

    simulation₂ :
      (Hgrd : guard ) →
        let m' := init Hgrd
        let (_,am') := abs₂.init () (strengthening₂ Hgrd)
        refine am' m'

-- instance [Machine CTX M] [Machine ACTX₁ AM₁] [Refinement AM₁ M] [Machine ACTX₂ AM₂] [Refinement AM₂ M]
--   (abs₁ : InitEvent AM₁ Unit Unit) (abs₂ : InitEvent AM₂ Unit Unit):
--   Coe (DoubleInitREvent'' AM₁ AM₂ M abs₁ abs₂) (DoubleInitREvent AM₁ AM₂ M (α := Unit) (β := Unit) abs₁ abs₂) where
--   coe ev := {
--               lift_in₁ := fun _ => ()
--               lift_in₂ := fun _ => ()
--               lift_out₁ := fun _ => ()
--               lift_out₂ := fun _ => ()
--               strengthening₁ _ m := ev.strengthening₁ m
--               strengthening₂ _ m := ev.strengthening₂ m
--               simulation₁ :=
--               fun x hgrd =>
--                 by
--                   simp
--                   exact ev.simulation₁ hgrd
--               simulation₂ :=
--               fun x hgrd  =>
--                 by
--                   simp
--                   exact ev.simulation₂ hgrd
--               guard _ := ev.guard
--               init x grd := ((), ev.init grd)
--               safety _ hgrd := ev.safety hgrd
--             }


-- @[simp]
-- def newDoubleInitREvent'' [Machine ACTX₁ AM₁] [Machine ACTX₂ AM₂] [Machine CTX M] [Refinement AM₁ M] [Refinement AM₂ M]
--   (abs₁ : InitEvent AM₁ Unit Unit)
--   (abs₂ : InitEvent AM₂ Unit Unit)
--   (ev: DoubleInitREvent'' AM₁ AM₂ M abs₁ abs₂)
--   :  DoubleInitREvent (α := Unit) (β := Unit) AM₁ AM₂ M abs₁ abs₂ := ev


-- ### Double refinement of anticipated events
