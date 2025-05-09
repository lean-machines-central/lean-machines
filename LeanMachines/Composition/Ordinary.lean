import Mathlib.Tactic

import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary
import LeanMachines.Refinement.Relational.Basic
import LeanMachines.Refinement.Relational.Ordinary


instance prod [m1 :Machine CTX₁ M₁] [ m2: Machine CTX₂ M₂] :
  Machine (CTX₁ × CTX₂) (M₁ × M₂)
  where
    context := ⟨m1.context,m2.context⟩
    invariant m := Machine.invariant m.1
                   ∧ Machine.invariant m.2
def composition
  [Machine CTX₁ M₁]
  (ev₁ : OrdinaryEvent M₁ α₁ β₁)
  [Machine CTX₂ M₂]
  (ev₂ : OrdinaryEvent M₂ α₂ β₂)
  : OrdinaryEvent (M₁ × M₂) (α₁× α₂) (β₁× β₂) :=
  newEvent
  {
    guard m x   := ev₁.guard m.1 x.1 ∧ ev₂.guard m.2 x.2
    action m x hgrd :=
      let (b₁,m₁) := ev₁.action m.1 x.1 hgrd.1
      let (b₂,m₂) := ev₂.action m.2 x.2 hgrd.2
      ((b₁,b₂),m₁,m₂)
    safety m x  :=
      by
        simp[Machine.invariant]
        intros hinv₁ hinv₂ hgrd
        constructor
        · exact ev₁.safety m.1 x.1 hinv₁ hgrd.1
        · exact ev₂.safety m.2 x.2 hinv₂ hgrd.2
  }

infixr:60 " © " => composition


instance instCompo [Machine CTX₁ M₁] [Machine CTX₂ M₂]
  (ev₁ : Event M₁ α₁ β₁) (ev₂ : Event M₂ α₂ β₂)
  [i₁ : SafeEventPO ev₁ (EventKind.TransDet (Convergence.Ordinary))]
  [i₂ : SafeEventPO ev₂ (EventKind.TransDet (Convergence.Ordinary))]:
  SafeEventPO (mkOrdinaryEvent ev₁ © mkOrdinaryEvent ev₂).toEvent (EventKind.TransDet (Convergence.Ordinary))
  (instM := prod)
  where
    safety m x :=
    by
      unfold Machine.invariant
      unfold prod
      simp[composition,mkOrdinaryEvent]
      intros hinv₁ hinv₂ hgrd
      constructor
      · exact i₁.safety m.1 x.1 hinv₁ hgrd.1
      · exact i₂.safety m.2 x.2 hinv₂ hgrd.2



instance compoMachine
  [Machine CTX₁ M₁] [Machine CTX₂ M₂] [Machine ACTX₁ AM₁] [Machine ACTX₂ AM₂]
  [ref₁ :Refinement AM₁ M₁] [ref₂ : Refinement AM₂ M₂] : Refinement (AM₁ × AM₂) (M₁ × M₂) where
  refine am m := Refinement.refine am.1 m.1 ∧ Refinement.refine am.2 m.2
  refine_safe am m  :=
    by
      unfold Machine.invariant
      unfold prod
      simp
      intros hinv₁ hinv₂ href₁ href₂
      constructor
      · exact ref₁.refine_safe am.1 m.1 hinv₁ href₁
      · exact ref₂.refine_safe am.2 m.2 hinv₂ href₂



instance RefinementComposition [Machine CTX₁ M₁] [Machine CTX₂ M₂]
  [Machine ACTX₁ AM₁] [Machine ACTX₂ AM₂]
  [ref₁ : Refinement AM₁ M₁] [ref₂ : Refinement AM₂ M₂]
  (ev₁ : OrdinaryEvent M₁ α₁ β₁) (ev₂ : OrdinaryEvent M₂ α₂ β₂)
  (abs₁ : OrdinaryEvent AM₁ α'₁ β'₁) (abs₂ : OrdinaryEvent AM₂ α'₂ β'₂)
  [sref₁ : SafeREventPO ev₁.toEvent abs₁.toEvent
    (instSafeEv := instSafeEventPO_OrdinaryEvent ev₁)
    (instSafeAbs := instSafeEventPO_OrdinaryEvent abs₁)
    (instR := ref₁)
    (valid_kind := by simp)]
  [sref₂ : SafeREventPO ev₂.toEvent abs₂.toEvent
    (instSafeEv := instSafeEventPO_OrdinaryEvent ev₂)
    (instSafeAbs := instSafeEventPO_OrdinaryEvent abs₂)
    (instR := ref₂)
    (valid_kind := by simp)]
  : SafeREventPO (ev₁ © ev₂).toEvent (abs₁ © abs₂).toEvent
    (instSafeEv := instSafeEventPO_OrdinaryEvent (ev₁ © ev₂))
    (instSafeAbs := instSafeEventPO_OrdinaryEvent (abs₁ © abs₂))
    (instR := compoMachine (ref₁ := ref₁) (ref₂ := ref₂))
    (valid_kind := by simp)
  where
    lift_in x := (sref₁.lift_in x.1, sref₂.lift_in x.2)
    lift_out x := (sref₁.lift_out x.1, sref₂.lift_out x.2)
    strengthening m x :=
      by
        simp[composition,Machine.invariant,Refinement.refine]
        intros hinv₁ hinv₂ hgrd₁ hgrd₂
        intros a b href₁ href₂
        constructor
        · exact sref₁.strengthening m.1 x.1 hinv₁ hgrd₁ a href₁
        · exact sref₂.strengthening m.2 x.2 hinv₂ hgrd₂ b href₂
    simulation m x :=
       by
        simp[composition,Machine.invariant,Refinement.refine]
        intros hinv hgrd a b href
        have hsim₁ := sref₁.simulation m.1 x.1 hinv.1 hgrd.1 a href.1
        simp at hsim₁
        have hsim₂ := sref₂.simulation m.2 x.2 hinv.2 hgrd.2 b href.2
        simp at hsim₂
        constructor
        · constructor
          · exact hsim₁.1
          · exact hsim₂.1
        · constructor
          · exact hsim₁.2
          · exact hsim₂.2













structure CountContext where
  max : Nat
  maxProp : max > 0


structure Counter0 (ctx : CountContext) where
  cpt : Nat


instance : Machine CountContext (Counter0 ctx) where
  context := ctx
  invariant c0 := c0.cpt ≤ ctx.max

def Counter0.Incr : OrdinaryEvent (Counter0 ctx) Nat Unit :=
  newEvent'
  {
    action := fun c0 v _ => {cpt:= c0.cpt + v}
    guard := fun c0 v => (c0.cpt + v) ≤ ctx.max
    safety := fun m v hinvm => by simp[Machine.invariant]
  }


#check Counter0.Incr © Counter0.Incr

structure DoubleCpt (ctx : CountContext × CountContext) where
  cpt₁ : Counter0 ctx.1
  cpt₂ : Counter0 ctx.2

def DoubleCpt.OfProd (p : Counter0 ctx₁ × Counter0 ctx₂) : DoubleCpt (ctx₁,ctx₂) :=
  ⟨p.1,p.2⟩


instance coed : Coe  (Counter0 ctx.1 × Counter0 ctx.2 ) (DoubleCpt ctx) where
  coe dcpt := ⟨dcpt.1, dcpt.2⟩



instance : Machine (CountContext × CountContext) (DoubleCpt ctx) where
  context := ctx
  invariant m := Machine.invariant m.1 ∧ Machine.invariant m.2

def DoubleCpt.OrdinaryOfProd (ev : OrdinaryEvent (Counter0 ctx₁ × Counter0 ctx₂) α β )
  : OrdinaryEvent (DoubleCpt (ctx₁,ctx₂)) α β :=
  {
    guard m := ev.guard (m.cpt₁,m.cpt₂)
    action m x grd :=
      let (r, m') := ev.action (m.cpt₁,m.cpt₂) x grd
      (r,m')
    safety m := ev.safety (m.cpt₁,m.cpt₂)
  }


-- Sadly, the coe doesn't work ?
def DoubleCpt.Incr : OrdinaryEvent (Counter0 ctx₁ × Counter0 ctx₂ ) (Nat × Nat) (Unit × Unit) :=
  Counter0.Incr (ctx := ctx₁) © Counter0.Incr (ctx := ctx₂)

def DoubleCpt.Incr' : OrdinaryEvent (DoubleCpt ctx) (Nat × Nat) (Unit × Unit) :=
  DoubleCpt.OrdinaryOfProd DoubleCpt.Incr



  -- coed.coe $ Counter0.Incr (ctx := ctx.1) © Counter0.Incr (ctx := ctx.2)
