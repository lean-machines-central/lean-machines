import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary
import LeanMachines.Event.Convergent
import LeanMachines.Refinement.Relational.Basic
import LeanMachines.Refinement.Relational.Ordinary
import LeanMachines.Refinement.Relational.Convergent


open Refinement



-- # Double refinement
structure OrdinaryREventbis (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  {α β α' β'} (abs : OrdinaryEvent AM α' β') (ev : OrdinaryEvent M α β)
  where

  /-- Transformation of input parameters: how a concrete parameter must be interpreted
  at the abstract level. -/
  lift_in : α → α'

  /-- Transformation of output value: how a concrete output must be interpreted
  at the abstract level. -/
  lift_out : β → β'

  /-- Proof obligation: guard strengthening. -/
  strengthening (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → ∀ am, refine am m
      → abs.guard am (lift_in x)

  /-- Proof obligation: action simulation. -/
  simulation (m : M) (x : α):
    (Hinv : Machine.invariant m)
    → (Hgrd : ev.guard m x)
    → ∀ am, (Href : refine am m)
      → let (y, m') := ev.action m x Hgrd
        let (z, am') := abs.action am (lift_in x) (strengthening m x Hinv Hgrd am Href)
        lift_out y = z ∧ refine am' m'



structure OrdinaryREventbis' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  {α α'} (abs : OrdinaryEvent AM α' Unit) (ev : OrdinaryEvent' M α)
  where

  /-- Transformation of input parameters: how a concrete parameter must be interpreted
  at the abstract level. -/
  lift_in : α → α'

  /-- Proof obligation: guard strengthening. -/
  strengthening (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → ∀ am, refine am m
      → abs.guard am (lift_in x)

  /-- Proof obligation: action simulation. -/
  simulation (m : M) (x : α):
    (Hinv : Machine.invariant m)
    → (Hgrd : ev.guard m x)
    → ∀ am, (Href : refine am m)
      → let m':= ev.action m x Hgrd
        let  (_,am') := abs.action am (lift_in x) (strengthening m x Hinv Hgrd am Href)
        refine am' m'

structure OrdinaryREventbis'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  (abs : OrdinaryEvent AM Unit Unit) (ev : OrdinaryEvent'' M)
  where
  /-- Proof obligation: guard strengthening. -/
  strengthening (m : M) :
    Machine.invariant m
    → ev.guard m
    → ∀ am, refine am m
      → abs.guard am ()

  /-- Proof obligation: action simulation. -/
  simulation (m : M) :
    (Hinv : Machine.invariant m)
    → (Hgrd : ev.guard m)
    → ∀ am, (Href : refine am m)
      → let m':= ev.action m Hgrd
        let (_, am') := abs.action am () (strengthening m Hinv Hgrd am Href)
        refine am' m'

-- We add a structure + smart constructor for the specific case where a concrete event refines two abstract events

structure MultiOrdinaryREvent
  {α β α'₁ β'₁ α'₂ β'₂}
  (AM₁) [Machine ACTX₁ AM₁]
  (AM₂) [Machine ACTX₂ AM₂]
  (abs₁ : OrdinaryEvent AM₁ α'₁ β'₁)
  (abs₂ : OrdinaryEvent AM₂ α'₂ β'₂)
  (M) [Machine CTX M] [instR₁ : Refinement AM₁ M] [instR₂ : Refinement AM₂ M]
  extends OrdinaryEvent M α β
  where
    ref₁ : OrdinaryREventbis AM₁ M abs₁ {action,guard,safety}
    ref₂ : OrdinaryREventbis AM₂ M abs₂ {action,guard,safety}

instance [Machine ACTX₁ AM₁] [Machine ACTX₂ AM₂] [Machine CTX M] [instR₁ : Refinement AM₁ M][instR₂ : Refinement AM₂ M]
  (abs₁ : OrdinaryEvent AM₁ α'₁ β'₁) (abs₂ : OrdinaryEvent AM₂ α'₂ β'₂)
  (ev : MultiOrdinaryREvent AM₁ AM₂
  abs₁
  abs₂
  M
  (α'₁ := α'₁)
  (β'₁ := β'₁)
  (α'₂ := α'₂)
  (β'₂ := β'₂)
  (instR₂ := instR₂) (instR₁ := instR₁)) :
  SafeREventPO
    (AM := AM₁) (M := M)
    (α := α) (β := β)
    (ev.toEvent (M := M)) (abs₁.toEvent (M := AM₁))
    (instSafeAbs := instSafeEventPO_OrdinaryEvent abs₁)
    (instSafeEv := instSafeEventPO_OrdinaryEvent ev.toOrdinaryEvent)
    (valid_kind := by simp)
  where
    lift_in := ev.ref₁.lift_in
    lift_out := ev.ref₁.lift_out
    strengthening := ev.ref₁.strengthening
    simulation := ev.ref₁.simulation


-- instance [Machine ACTX₁ AM₁] [Machine ACTX₂ AM₂] [Machine CTX M] [instR₁ : Refinement AM₁ M][instR₂ : Refinement AM₂ M]
--   -- (abs₁ : OrdinaryEvent AM₁ α'₁ β'₁) (abs₂ : OrdinaryEvent AM₂ α'₂ β'₂)
--   (ev : MultiOrdinaryREvent AM₁ AM₂ M
--     (α'₁ := α'₁)
--     (β'₁ := β'₁)
--     (α'₂ := α'₂)
--     (β'₂ := β'₂)
--     (instR₂ := instR₂) (instR₁ := instR₁)) :
--   SafeREventPO
--     (AM := AM₂) (M := M)
--     (α := α) (β := β)
--     (ev.toEvent (M := M)) (ev.abs₂.toEvent (M := AM₂))
--     (instSafeAbs := instSafeEventPO_OrdinaryEvent ev.abs₂)
--     (instSafeEv := instSafeEventPO_OrdinaryEvent ev.toOrdinaryEvent)
--     (valid_kind := by simp)
--   where
--     lift_in := ev.ref₂.lift_in
--     lift_out := ev.ref₂.lift_out
--     strengthening := ev.ref₂.strengthening
--     simulation := ev.ref₂.simulation

@[simp]
def newMultiOrdinaryREvent [Machine ACTX₁ AM₁] [Machine ACTX₂ AM₂] [Machine CTX M] [Refinement AM₁ M] [Refinement AM₂ M]
    (abs₁ : OrdinaryEvent AM₁ α'₁ β'₁) (abs₂ : OrdinaryEvent AM₂ α'₂ β'₂)
  (ev: MultiOrdinaryREvent AM₁ AM₂ abs₁ abs₂ M  (α := α) (β := β) (α'₁ := α'₁)
    (β'₁ := β'₁)
    (α'₂ := α'₂)
    (β'₂ := β'₂))
  :  MultiOrdinaryREvent AM₁ AM₂ abs₁ abs₂ M (α := α) (β := β) (α'₁ := α'₁)
    (β'₁ := β'₁)
    (α'₂ := α'₂)
    (β'₂ := β'₂):= ev


-- /-Smart constructors for when the output has type unit -/

-- structure MultiOrdinaryREvent'
--   {α}
--   (AM₁) [Machine ACTX₁ AM₁]
--   (AM₂) [Machine ACTX₂ AM₂]
--   (M) [Machine CTX M] [instR₁ : Refinement AM₁ M] [instR₂ : Refinement AM₂ M]
--   (abs₁ : OrdinaryEvent AM₁ α'₁ Unit)
--   (abs₂ : OrdinaryEvent AM₂ α'₂ Unit)
--   extends OrdinaryEvent' M α
--   where
--     ref₁ : OrdinaryREventbis' AM₁ M abs₁ {action,guard,safety}
--     ref₂ : OrdinaryREventbis' AM₂ M abs₂ {action,guard,safety}



-- instance {α} [Machine CTX M] [Machine ACTX₁ AM₁] [Refinement AM₁ M] [Machine ACTX₂ AM₂] [Refinement AM₂ M]
--   (abs₁ : OrdinaryEvent AM₁ α'₁ Unit) (abs₂ : OrdinaryEvent AM₂ α'₂ Unit):
--   Coe (MultiOrdinaryREvent' (α := α) AM₁ AM₂ M abs₁ abs₂) (MultiOrdinaryREvent AM₁ AM₂ M (α := α) (β := Unit) abs₁ abs₂) where
--   coe ev := {
--               guard := ev.guard
--               action m x grd := ((), ev.action m x grd)
--               safety := ev.safety

--               ref₁ := {
--                 lift_in := ev.ref₁.lift_in
--                 lift_out := fun _ => ()
--                 strengthening := ev.ref₁.strengthening
--                 simulation :=
--                   fun m x hinv hgrd am href =>
--                     by
--                       simp
--                       exact ev.ref₁.simulation m x hinv hgrd am href
--               }
--               ref₂ := {
--                 lift_in := ev.ref₂.lift_in
--                 lift_out := fun _ => ()
--                 strengthening := ev.ref₂.strengthening
--                 simulation :=
--                 fun m x hinv hgrd am href =>
--                     by
--                       simp
--                       exact ev.ref₂.simulation m x hinv hgrd am href
--               }

--             }

-- @[simp]
-- def newMultiOrdinaryREvent' [Machine ACTX₁ AM₁] [Machine ACTX₂ AM₂] [Machine CTX M] [Refinement AM₁ M] [Refinement AM₂ M]
--   (abs₁ : OrdinaryEvent AM₁ α'₁ Unit )
--   (abs₂ : OrdinaryEvent AM₂ α'₂ Unit )
--   (ev: MultiOrdinaryREvent' AM₁ AM₂ M abs₁ abs₂ (α := α ))
--   :  MultiOrdinaryREvent AM₁ AM₂ M abs₁ abs₂ (α := α ) (β := Unit) := ev


-- /- Smart constructor when both the input and the output are of type Unit -/



-- structure MultiOrdinaryREvent''
--   (AM₁) [Machine ACTX₁ AM₁]
--   (AM₂) [Machine ACTX₂ AM₂]
--   (M) [Machine CTX M] [instR₁ : Refinement AM₁ M] [instR₂ : Refinement AM₂ M]
--   (abs₁ : OrdinaryEvent AM₁ Unit Unit )
--   (abs₂ : OrdinaryEvent AM₂ Unit Unit )
--   extends OrdinaryEvent'' M
--   where
--     -- First refinement
--     ref₁ : OrdinaryREventbis'' AM₁ M abs₁ {action,guard,safety}
--     ref₂ : OrdinaryREventbis'' AM₂ M abs₂ {action,guard,safety}



-- instance [Machine CTX M] [Machine ACTX₁ AM₁] [Refinement AM₁ M] [Machine ACTX₂ AM₂] [Refinement AM₂ M]
--   (abs₁ : OrdinaryEvent AM₁ Unit Unit) (abs₂ : OrdinaryEvent AM₂ Unit Unit):
--   Coe (MultiOrdinaryREvent'' AM₁ AM₂ M abs₁ abs₂) (MultiOrdinaryREvent AM₁ AM₂ M (α := Unit) (β := Unit) abs₁ abs₂) where
--   coe ev := {
--               guard m x := ev.guard m
--               action m x grd := ((), ev.action m grd)
--               safety m x := ev.safety m
--               ref₁ := {
--                 lift_in := fun _ => ()
--                 lift_out := fun _ => ()
--                 strengthening m _ hgrd :=
--                   by
--                     simp
--                     exact (ev.ref₁.strengthening m hgrd)
--                 simulation :=
--                   fun m x hinv hgrd am href =>
--                     by
--                       simp
--                       exact ev.ref₁.simulation m hinv hgrd am href
--               }
--               ref₂ := {
--                 lift_in := fun _ => ()
--                 lift_out := fun _ => ()
--                 strengthening m _ hgrd :=
--                   by
--                     simp
--                     exact (ev.ref₂.strengthening m hgrd)
--                 simulation :=
--                   fun m x hinv hgrd am href =>
--                     by
--                       simp
--                       exact ev.ref₂.simulation m hinv hgrd am href
--               }
--             }

-- @[simp]
-- def newMultiOrdinaryREvent'' [Machine ACTX₁ AM₁] [Machine ACTX₂ AM₂] [Machine CTX M] [Refinement AM₁ M] [Refinement AM₂ M]
--   (abs₁ : OrdinaryEvent AM₁ Unit Unit)
--   (abs₂ : OrdinaryEvent AM₂ Unit Unit)
--   (ev: MultiOrdinaryREvent'' AM₁ AM₂ M abs₁ abs₂ )
--   :  MultiOrdinaryREvent AM₁ AM₂ M abs₁ abs₂ (α := Unit) (β := Unit) := ev


-- ### Multi refinement of init events


structure SafeInitREventbis (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR : Refinement AM M]
  {α β α' β'} (abs : InitEvent AM α' β') (ev : InitEvent M α β ) where
  lift_in : α → α'
  lift_out : β → β'

  strengthening (x : α) : ev.guard x → abs.guard (lift_in x)

  simulation (x : α) :
    (Hgrd : ev.guard x) →
      let (y, m') := ev.init x Hgrd
      let (z, am') := abs.init (lift_in x) (strengthening x Hgrd)
      lift_out y = z ∧ refine am' m'
structure SafeInitREventbis' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR : Refinement AM M]
  {α α'} (abs : InitEvent AM α' Unit) (ev : InitEvent' M α) where
  lift_in : α → α'

  strengthening (x : α) : ev.guard x → abs.guard (lift_in x)

  simulation (x : α) :
    (Hgrd : ev.guard x) →
      let (m') := ev.init x Hgrd
      let (_, am') := abs.init (lift_in x) (strengthening x Hgrd)
      refine am' m'
structure SafeInitREventbis'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR : Refinement AM M]
  (abs : InitEvent AM Unit Unit) (ev : InitEvent'' M) where
  strengthening : ev.guard  → abs.guard ()
  simulation  :
    (Hgrd : ev.guard ) →
      let (m') := ev.init Hgrd
      let (_, am') := abs.init () (strengthening Hgrd)
      refine am' m'


structure MultiInitREvent
  {α β}
  (AM₁) [Machine ACTX₁ AM₁]
  (AM₂) [Machine ACTX₂ AM₂]
  (M) [Machine CTX M] [instR₁ : Refinement AM₁ M] [instR₂ : Refinement AM₂ M]
  (abs₁ : InitEvent AM₁ α'₁ β'₁)
  (abs₂ : InitEvent AM₂ α'₂ β'₂)
  extends InitEvent M α β
  where
    ref₁ : SafeInitREventbis AM₁ M abs₁ {init,guard,safety}
    ref₂ : SafeInitREventbis AM₂ M abs₂ {init,guard,safety}

instance [Machine ACTX₁ AM₁] [Machine ACTX₂ AM₂] [Machine CTX M] [instR₁ : Refinement AM₁ M][instR₂ : Refinement AM₂ M]
  (abs₁ : InitEvent AM₁ α'₁ β'₁) (abs₂ : InitEvent AM₂ α'₂ β'₂)
  (ev : MultiInitREvent AM₁ AM₂ M abs₁ abs₂ (instR₂ := instR₂) (instR₁ := instR₁)) :
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
  (ev : MultiInitREvent AM₁ AM₂ M abs₁ abs₂ (instR₂ := instR₂) (instR₁ := instR₁)) :
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


def newMultiInitREvent [Machine ACTX₁ AM₁] [Machine ACTX₂ AM₂] [Machine CTX M] [Refinement AM₁ M] [Refinement AM₂ M]
  (abs₁ : InitEvent AM₁ α'₁ β'₁)
  (abs₂ : InitEvent AM₂ α'₂ β'₂)
  (ev: MultiInitREvent AM₁ AM₂ M abs₁ abs₂ (α := α) (β := β))
  :  MultiInitREvent AM₁ AM₂ M abs₁ abs₂ (α := α) (β := β) := ev


/- Smart constructor for when the init has Unit as output type -/


structure MultiInitREvent'
  {α}
  (AM₁) [Machine ACTX₁ AM₁]
  (AM₂) [Machine ACTX₂ AM₂]
  (M) [Machine CTX M] [instR₁ : Refinement AM₁ M] [instR₂ : Refinement AM₂ M]
  (abs₁ : InitEvent AM₁ α'₁ Unit)
  (abs₂ : InitEvent AM₂ α'₂ Unit)
  extends InitEvent' M α
  where
    ref₁ : SafeInitREventbis' AM₁ M abs₁ {init,guard,safety}
    ref₂ : SafeInitREventbis' AM₂ M abs₂ {init,guard,safety}

instance {α} [Machine CTX M] [Machine ACTX₁ AM₁] [Refinement AM₁ M] [Machine ACTX₂ AM₂] [Refinement AM₂ M]
  (abs₁ : InitEvent AM₁ α'₁ Unit) (abs₂ : InitEvent AM₂ α'₂ Unit):
  Coe (MultiInitREvent' (α := α) AM₁ AM₂ M abs₁ abs₂) (MultiInitREvent AM₁ AM₂ M (α := α) (β := Unit) abs₁ abs₂) where
  coe ev := {
              ref₁ := {
                lift_in := ev.ref₁.lift_in
                lift_out := (fun _ => ())
                strengthening := ev.ref₁.strengthening
                simulation :=
                (fun x hgrd =>
                  by
                    simp
                    exact ev.ref₁.simulation x hgrd)
              }
              ref₂ :=  {
                lift_in := ev.ref₂.lift_in
                lift_out := (fun _ => ())
                strengthening := ev.ref₂.strengthening
                simulation :=
                (fun x hgrd =>
                  by
                    simp
                    exact ev.ref₂.simulation x hgrd)
              }
              guard := ev.guard
              init x grd := ((), ev.init x grd)
              safety := ev.safety
            }

@[simp]
def newMultiInitREvent' [Machine ACTX₁ AM₁] [Machine ACTX₂ AM₂] [Machine CTX M] [Refinement AM₁ M] [Refinement AM₂ M]
  (abs₁ : InitEvent AM₁ α'₁ Unit )
  (abs₂ : InitEvent AM₂ α'₂ Unit )
  (ev: MultiInitREvent' AM₁ AM₂ M abs₁ abs₂ (α := α) )
  :  MultiInitREvent AM₁ AM₂ M abs₁ abs₂ (α := α ) (β := Unit) := ev


structure MultiInitREvent''
  (AM₁) [Machine ACTX₁ AM₁]
  (AM₂) [Machine ACTX₂ AM₂]
  (M) [Machine CTX M] [instR₁ : Refinement AM₁ M] [instR₂ : Refinement AM₂ M]
  (abs₁ : InitEvent AM₁ Unit Unit)
  (abs₂ : InitEvent AM₂ Unit Unit)
  extends InitEvent'' M
  where
    ref₁ : SafeInitREventbis'' AM₁ M abs₁ {init,guard,safety}
    ref₂ : SafeInitREventbis'' AM₂ M abs₂ {init,guard,safety}

instance [Machine CTX M] [Machine ACTX₁ AM₁] [Refinement AM₁ M] [Machine ACTX₂ AM₂] [Refinement AM₂ M]
  (abs₁ : InitEvent AM₁ Unit Unit) (abs₂ : InitEvent AM₂ Unit Unit):
  Coe (MultiInitREvent'' AM₁ AM₂ M abs₁ abs₂) (MultiInitREvent AM₁ AM₂ M (α := Unit) (β := Unit) abs₁ abs₂) where
  coe ev := {
              ref₁ := {
                lift_in := fun _ => ()
                lift_out := fun _ => ()
                strengthening _ m := ev.ref₁.strengthening m
                simulation :=
                (fun x hgrd =>
                  by
                    simp
                    exact ev.ref₁.simulation hgrd)
              }
              ref₂ :=  {
                lift_in := fun _ => ()
                lift_out := fun _ => ()
                strengthening _ m := ev.ref₂.strengthening m
                simulation :=
                (fun x hgrd =>
                  by
                    simp
                    exact ev.ref₂.simulation hgrd)
              }
              guard _ := ev.guard
              init x grd := ((), ev.init grd)
              safety _  hgrd := ev.safety hgrd
            }


@[simp]
def newMultiInitREvent'' [Machine ACTX₁ AM₁] [Machine ACTX₂ AM₂] [Machine CTX M] [Refinement AM₁ M] [Refinement AM₂ M]
  (abs₁ : InitEvent AM₁ Unit Unit)
  (abs₂ : InitEvent AM₂ Unit Unit)
  (ev: MultiInitREvent'' AM₁ AM₂ M abs₁ abs₂)
  :  MultiInitREvent (α := Unit) (β := Unit) AM₁ AM₂ M abs₁ abs₂ := ev


-- ### Double refinement of anticipated events
