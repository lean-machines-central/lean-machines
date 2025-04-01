import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary
import LeanMachines.Refinement.Relational.Basic
import LeanMachines.Refinement.Relational.Convergent
import LeanMachines.Refinement.Relational.Ordinary
import LeanMachines.Refinement.Relational.Double
import LeanMachines.Examples.Multiref.Tank.Counter0
import LeanMachines.Examples.Multiref.Tank.Xor0

/-
   # Multi-refinement example : the tank example

   ## The Concrete machine : a tank with a maximum capacity and two doors that can't be simultaneously opened

   This concrete machine refines both the counter (for it has a maximum capacity that can be abstracted
   as a counter with an upper bound) and the Xor between two booleans (for the two doors cannot be
   simultaneously opened)
-/


/- The concrete machine -/
inductive status where | OPEN_IN | OPEN_OUT | CLOSED
    deriving Repr, BEq, DecidableEq

structure Tank1 (ctx : CountContext) extends (Counter0 ctx) where
    st : status


instance : Machine CountContext (Tank1 ctx) where
    context := ctx
    invariant := fun m => (m.cpt ≤ ctx.max)
        ∧ (m.st = status.OPEN_IN → m.cpt < ctx.max)
        ∧ (m.st = status.OPEN_OUT → m.cpt > 0)

/- Refinement of the counter -/
instance : Refinement (Counter0 ctx) (Tank1 ctx) where
    refine := fun am m => am.cpt = m.cpt
    refine_safe :=
        fun c0 t1 =>
            by
                simp[Machine.invariant]
                intros hinv₁ _ _ href
                rw[href]
                exact hinv₁

/- Refinement of the Xor -/
instance : Refinement (Xor0 ctx₀) (Tank1 ctx) where
    refine x0 t1 :=
        (x0.x → t1.st = status.OPEN_IN)  ∧
        (x0.y → t1.st = status.OPEN_OUT) ∧
        ((¬x0.x ∧ ¬x0.y) ↔ (t1.st = status.CLOSED)) ∧
        ((x0.x ∧ ¬ x0.y) ↔ (t1.st = status.OPEN_IN)) ∧
        ((¬x0.x ∧ x0.y)  ↔ (t1.st = status.OPEN_OUT))
    refine_safe :=
        fun d0 t1 =>
            by
                simp[Machine.invariant]
                intros hinv₁ _ _ href₁ href₂ href₃ href₄ href₅ hb_in
                have hopen_in := (href₁ hb_in)
                have ⟨hl₄,hr₄⟩ := href₄
                have hdb := (hr₄ hopen_in)
                have ⟨_,hb_out⟩ := hdb
                assumption

/- Init of the tank machine -/

def Tank1.Init : DoubleInitREvent'' (Counter0 ctx) (Xor0 ctx₀) (Tank1 ctx) Counter0.Init Xor0.Init :=
    newDoubleInitREvent''
        Counter0.Init
        Xor0.Init
        {
            init := fun _ => {cpt := 0, st := status.CLOSED}
            safety m := by simp[Machine.invariant]
            guard := True
            strengthening₁ :=
                by
                    simp[Machine.invariant,Counter0.Init]
            strengthening₂ :=
                by
                    simp[Machine.invariant, Xor0.Init]
            simulation₁ :=
                by
                    simp[Refinement.refine,Counter0.Init]
            simulation₂ :=
                by
                    simp[Refinement.refine,Xor0.Init]
        }


-- /- First event : filling up the tank, without touching the doors-/
-- def Tank1.fill : Event (Tank1 ctx) Nat Unit :=
--   {
--     action := fun t1 v _ => ((),
--         {   cpt:= t1.cpt + v,
--             st := t1.st
--         })
--     guard :=
--         fun t1 v => (t1.st = status.OPEN_IN) ∧ (t1.cpt + v < ctx.max) ∧ (v > 0)
--   }

-- /- it is a Convergent Event -/
-- instance instFill : ConvergentEventPO Nat (Tank1.fill (ctx:=ctx)) where
--     safety := fun m v =>
--         by
--             simp[Machine.invariant, Tank1.fill]
--             omega
--     variant := fun m => ctx.max - m.cpt
--     convergence :=
--     fun m x =>
--         by
--             simp[Tank1.fill]
--             intros hinv hgrd₁ hgrd₂ hgrd₃
--             omega

-- /- It refines the Incr event of the counter, which is only possible because
-- it is not an ordinary event (thus we can discharge the PO valid_kind) -/
-- instance : SafeREvent
--     (instSafeEv := instFill.toSafeEvent)
--     (instSafeAbs := instIncrAnt.toSafeEvent)
--     (Tank1.fill (ctx := ctx)) (Counter0.Incr (ctx :=ctx))
--     (valid_kind := by simp)
--     where
--     lift_in := id
--     lift_out := id
--     strengthening :=
--         fun m x =>
--             by
--                 simp[Machine.invariant,Counter0.Incr,Refinement.refine,Tank1.fill]
--                 intros _ _ _ _ _ _ _ href
--                 rw[href]
--                 omega
--     simulation :=
--         fun m x =>
--             by
--                 simp[Machine.invariant,Counter0.Incr,Refinement.refine,Tank1.fill]

-- /- As we don't modify the status of the door, it refines the skip event of the Xor machine

--     A convergent event can refine an ordinary one so the kinds are compatible
--     (as shown with the valid_kind PO)
--  -/
-- instance : SafeREvent
--     (instSafeEv := instFill.toSafeEvent)
--     (instSafeAbs := instSkip)
--     (Tank1.fill (ctx := ctx)) (skip_Event (Xor0 ctx₀) Unit)
--     (valid_kind :=
--         by simp
--     ) where
--     lift_in := fun _ => ()
--     lift_out := id
--     strengthening :=
--         fun m x => by simp
--     simulation :=
--         fun m x =>
--             by
--                 simp[Machine.invariant, Refinement.refine,Tank1.fill]

-- /- Second event : filling up the tank to its maximum capacity and automatically closing the door -/

-- def Tank1.fillUp : Event (Tank1 ctx) Unit Unit :=
--     {
--         action _ _ _ :=
--         ((),
--             {
--                 cpt := ctx.max,
--                 st := status.CLOSED
--             }
--         )
--         guard t1 _ :=  t1.st = status.OPEN_IN
--     }

-- /- It is a SafeEvent -/
-- instance instFillUp : ConvergentEventPO Nat (Tank1.fillUp (ctx :=ctx)) where
--     variant := fun m => ctx.max - m.cpt
--     safety m _ := by simp[Machine.invariant,Tank1.fillUp]
--     convergence :=
--         fun m =>
--             by
--                 simp[Machine.invariant,Tank1.fillUp]
--                 intros hinv₁ hinv₂ hinv₃ hgrd₁
--                 exact (hinv₂ hgrd₁)

-- /- It refines the Incr event of the counter -/
-- instance : SafeREvent
--     (instSafeEv := instFillUp.toSafeEvent)
--     (instSafeAbs := instSetCountSf)
--     (Tank1.fillUp (ctx := ctx)) (Counter0.setCount (ctx:= ctx))
--     (valid_kind :=
--         by
--             simp
--     )
--     where
--     lift_in := fun _ => ctx.max
--     lift_out := id
--     strengthening m x:=
--         by
--             simp[Machine.invariant,Refinement.refine, Counter0.setCount,Tank1.fillUp]

--     simulation m x :=
--         by
--             simp[Machine.invariant,Refinement.refine, Counter0.setCount,Tank1.fillUp]



-- /- It also refines the event SetX_false of the Xor -/
-- instance : SafeREvent
--         (Tank1.fillUp (ctx:= ctx)) (Xor0.SetX_false (ctx:= ctx'))
--         (instSafeEv := instFillUp.toSafeEvent)
--         (instSafeAbs := instSetXf)
--         (valid_kind := by simp)
--     where
--     lift_in := fun _ => ()
--     lift_out := id
--     strengthening m x := by simp[Xor0.SetX_false]
--     simulation m x :=
--         by
--             simp[Machine.invariant,Refinement.refine,Tank1.fillUp,Xor0.SetX_false]
--             intros hinv₁ _ _ hgrd₁ am href₁ href₂ href₃ href₄ href₅
--             simp[hgrd₁] at href₄
--             exact href₄.2


-- /- -/
-- def Tank1.drain : Event (Tank1 ctx) Nat Unit :=
--     {
--         action m v _ := ((),{cpt := m.cpt - v, st := m.st})
--         guard m v := m.st = status.OPEN_OUT ∧ m.cpt - v > 0 ∧ v > 0
--     }

-- instance instDrain : ConvergentEventPO Nat (Tank1.drain (ctx:=ctx)) where
--     safety m v :=
--     by
--         simp[Machine.invariant,Tank1.drain]
--         intros hinv₁ hinv₂ hinv₃ hgrd₁ hgrd₂ _
--         constructor
--         · omega
--         constructor
--         ·   intro h
--             rw[h] at hgrd₁
--             contradiction
--         ·   intro _
--             assumption

--     variant := fun m => m.cpt
--     convergence := fun m x =>
--         by
--             simp[Machine.invariant, Variant.variant,Tank1.drain]
--             intros hinv₁ hinv₂ hinv₃ hgrd₁ hgrd₂ hgrd₃
--             exact And.intro (hinv₃ hgrd₁) hgrd₃

-- instance : SafeREvent
--     (Tank1.drain (ctx:= ctx)) (Counter0.Decr (ctx:=ctx))
--     (instSafeEv := instDrain.toSafeEvent)
--     (instSafeAbs := instDecrCvg.toSafeEvent)
--     (valid_kind := by simp)
--     where
--     lift_in := id
--     lift_out := id
--     strengthening := by
--         simp[Machine.invariant,Refinement.refine,Tank1.drain, Counter0.Decr]
--         intros
--         omega
--     simulation m x :=
--         by
--             simp[Machine.invariant, Refinement.refine, Tank1.drain, Counter0.Decr]
--             intros hinv _ _ hgrd₁ hgrd₂ _ am href
--             rw[href]

-- instance : SafeREvent
--     (instSafeEv := instDrain.toSafeEvent)
--     (instSafeAbs := instSkip)
--     (Tank1.drain (ctx:= ctx)) (skip_Event (Xor0 ctx₀) Unit)
--     (valid_kind := by simp)
--     where
--     lift_in := fun _ => ()
--     lift_out := id
--     strengthening m x := by simp[Machine.invariant, Refinement.refine]
--     simulation := by simp[Machine.invariant,Refinement.refine, Tank1.drain]



-- def Tank1.drainAll : Event (Tank1 ctx) Unit Unit :=
--     {
--         action _ _ _ := ((), {cpt :=0,st:= status.CLOSED})
--         guard m _ := m.st = status.OPEN_OUT
--     }


-- instance instDrainAll : ConvergentEventPO Nat (Tank1.drainAll (ctx := ctx))  where
--     safety := by simp[Machine.invariant,Tank1.drainAll]
--     variant := fun m => m.cpt
--     convergence :=
--         fun m x =>
--             by
--                 simp[Machine.invariant,Variant.variant,Tank1.drainAll]


-- instance : SafeREvent
--     (Tank1.drainAll (ctx:=ctx)) (Counter0.setCount (ctx:=ctx))
--     (instSafeEv := instDrainAll.toSafeEvent)
--     (instSafeAbs := instSetCountSf)
--     (valid_kind := by simp)
--     where
--     lift_in :=  fun _ => 0
--     lift_out := id
--     strengthening :=
--         fun m  x =>
--             by
--                 simp[Machine.invariant,Refinement.refine,Counter0.setCount,Tank1.drainAll]
--     simulation :=
--         by
--             simp[Machine.invariant,Refinement.refine, Counter0.setCount,Tank1.drainAll]


-- instance : SafeREvent (Tank1.drainAll (ctx := ctx)) (Xor0.SetY_false (ctx:=ctx'))
--     (instSafeEv := instDrainAll.toSafeEvent)
--     (instSafeAbs := instSetYf)
--     (valid_kind := by simp)
--     where
--     lift_in := fun _ => ()
--     lift_out := id
--     strengthening :=
--         by
--             simp[Machine.invariant,Refinement.refine,Xor0.SetY_false,Tank1.drainAll]
--             intros m _ _ _ hgrd am href₁ href₂ href₃ href₄ href₅
--             simp[hgrd] at href₅
--             exact (href₅.1)
--     simulation :=
--         by
--             simp[Machine.invariant,Refinement.refine,Xor0.SetY_false,Tank1.drainAll]
--             intros m _ _ _ hgrd am href₁ href₂ href₃ href₄ href₅
--             simp[hgrd] at href₅
--             exact (href₅.1)


-- def Tank1.Open_Door_in : Event (Tank1 ctx) Unit Unit :=
--     {
--         action m _ _ := ((), {cpt := m.cpt, st := status.OPEN_IN})
--         guard m _ := m.st ≠ status.OPEN_OUT ∧ m.cpt < ctx.max
--     }

-- instance instOpenIn : SafeEventPO (Tank1.Open_Door_in (ctx:= ctx)) (EventKind.TransDet (Convergence.Ordinary)) where
--     safety :=
--         by
--             simp[Machine.invariant,Tank1.Open_Door_in]
--             intros m _ _ hgrd₁ _ _
--             constructor
--             · assumption
--             . assumption

-- instance : SafeREvent (Tank1.Open_Door_in (ctx := ctx)) (skip_Event (Counter0 ctx) Unit)
--     (instSafeEv := instOpenIn)
--     (instSafeAbs := instSkip)
--     (valid_kind := by simp)
--     where
--     lift_in := id
--     lift_out := id
--     strengthening m x:= by simp
--     simulation := by simp[Machine.invariant,Refinement.refine,Tank1.Open_Door_in]

-- instance : SafeREvent (Tank1.Open_Door_in (ctx:= ctx)) (Xor0.SetX_true (ctx:= ctx'))
--     (instSafeEv := instOpenIn)
--     (instSafeAbs := instSetXt)
--     (valid_kind := by simp)
--     where
--     lift_in := id
--     lift_out := id
--     strengthening m x :=
--         by
--             simp[Refinement.refine,Tank1.Open_Door_in,Xor0.SetX_true]
--             intros hinv hgrd
--             simp[hgrd]
--             intros
--             assumption
--     simulation m x :=
--         by
--             simp[Machine.invariant,Refinement.refine,Tank1.Open_Door_in,Xor0.SetX_true]
--             intros hinv _ _ hgrd
--             simp[hgrd]
--             intros
--             assumption

-- def Tank1.Close_Door_in : Event (Tank1 ctx) Unit Unit :=
--     {
--         action m _ _ := ((),{cpt:= m.cpt, st := status.CLOSED})
--         guard m _ := m.st = status.OPEN_IN
--     }

-- instance instCloseIn : SafeEventPO (Tank1.Close_Door_in (ctx:= ctx)) (EventKind.TransDet (Convergence.Ordinary)) where
--     safety m x :=
--         by
--             simp[Machine.invariant,Tank1.Close_Door_in]
--             intros
--             assumption

-- instance : SafeREvent (Tank1.Close_Door_in (ctx := ctx)) (skip_Event (Counter0 ctx) Unit)
--     (instSafeEv := instCloseIn)
--     (instSafeAbs := instSkip)
--     (valid_kind := by simp) where
--     lift_in := id
--     lift_out := id
--     strengthening m x:= by simp
--     simulation := by simp[Machine.invariant,Refinement.refine,Tank1.Close_Door_in]

-- instance : SafeREvent (Tank1.Close_Door_in (ctx:= ctx)) (Xor0.SetX_false (ctx:= ctx'))
--     (instSafeEv := instCloseIn)
--     (instSafeAbs := instSetXf)
--     (valid_kind := by simp)
--     where
--     lift_in := id
--     lift_out := id
--     strengthening m x :=
--         by
--             simp[Refinement.refine,Tank1.Close_Door_in,Xor0.SetX_false]
--     simulation m x :=
--         by
--             simp[Machine.invariant,Refinement.refine,Tank1.Close_Door_in,Xor0.SetX_false]
--             intros hinv _ _ hgrd
--             simp[hgrd]
--             intros
--             assumption



-- def Tank1.Open_Door_out : Event (Tank1 ctx) Unit Unit :=
--     {
--         action m _ _ := ((), {cpt := m.cpt, st := status.OPEN_OUT})
--         guard m _ := m.st ≠ status.OPEN_IN ∧ m.cpt > 0
--     }

-- instance instOpenOut : SafeEventPO (Tank1.Open_Door_out (ctx:= ctx)) (EventKind.TransDet (Convergence.Ordinary)) where
--     safety :=
--         by
--             simp[Machine.invariant,Tank1.Open_Door_out]
--             intros m hinv₁ hinv₂ hinv₃ hgrd₁ hgrd₂
--             apply And.intro (hinv₁) (hgrd₂)

-- instance : SafeREvent (Tank1.Open_Door_out (ctx := ctx)) (skip_Event (Counter0 ctx) Unit)
--     (instSafeEv := instOpenOut)
--     (instSafeAbs := instSkip)
--     (valid_kind := by simp)
--     where
--     lift_in := id
--     lift_out := id
--     strengthening m x:= by simp
--     simulation := by simp[Machine.invariant,Refinement.refine,Tank1.Open_Door_out]

-- instance : SafeREvent (Tank1.Open_Door_out (ctx:= ctx)) (Xor0.SetY_true (ctx:= ctx'))
--     (instSafeEv := instOpenOut)
--     (instSafeAbs := instSetYt)
--     (valid_kind := by simp)
--     where
--     lift_in := id
--     lift_out := id
--     strengthening m x :=
--         by
--             simp[Refinement.refine,Tank1.Open_Door_out,Xor0.SetY_true]
--             intros hinv hgrd
--             simp[hgrd]
--             intros
--             assumption
--     simulation m x :=
--         by
--             simp[Machine.invariant,Refinement.refine,Tank1.Open_Door_out,Xor0.SetY_true]
--             intros hinv _ _ hgrd
--             simp[hgrd]
--             intros
--             assumption

-- def Tank1.Close_Door_out : Event (Tank1 ctx) Unit Unit :=
--     {
--         action m _ _ := ((),{cpt:= m.cpt, st := status.CLOSED})
--         guard m _ := m.st = status.OPEN_OUT
--     }

-- instance instCloseOut : SafeEventPO (Tank1.Close_Door_out (ctx:= ctx)) (EventKind.TransDet (Convergence.Ordinary)) where
--     safety m x :=
--         by
--             simp[Machine.invariant,Tank1.Close_Door_out]
--             intros
--             assumption

-- instance : SafeREvent (Tank1.Close_Door_out (ctx := ctx)) (skip_Event (Counter0 ctx) Unit)
--     (instSafeEv := instCloseOut)
--     (instSafeAbs := instSkip)
--     (valid_kind := by simp)

--     where
--     lift_in := id
--     lift_out := id
--     strengthening m x:= by simp
--     simulation := by simp[Machine.invariant,Refinement.refine,Tank1.Close_Door_out]

-- instance : SafeREvent (Tank1.Close_Door_out (ctx:= ctx)) (Xor0.SetY_false (ctx:= ctx'))
--     (instSafeEv := instCloseOut)
--     (instSafeAbs := instSetYf)
--     (valid_kind := by simp)

--     where
--     lift_in := id
--     lift_out := id
--     strengthening m x :=
--         by
--             simp[Refinement.refine,Tank1.Close_Door_out,Xor0.SetY_false]
--             intros _ hgrd
--             simp[hgrd]
--             intros
--             assumption
--     simulation m x :=
--         by
--             simp[Machine.invariant,Refinement.refine,Tank1.Close_Door_out,Xor0.SetY_false]
--             intros hinv _ _ hgrd
--             simp[hgrd]
--             intros
--             assumption
