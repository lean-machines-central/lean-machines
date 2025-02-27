import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary
import LeanMachines.Refinement.Relational.Basic
import LeanMachines.Examples.Counter0
import LeanMachines.Examples.Xor0

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

/- Refinement of the counter -/
instance : Refinement (Counter0 ctx) (Tank1 ctx) where
    refine := fun am m => am.cpt = m.cpt
    refine_safe :=
        fun c0 t1 =>
            by
                simp[Machine.invariant]
                intros hinv₁ href
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
                intros hinv₁ href₁ href₂ href₃ href₄ href₅ hb_in
                have hopen_in := (href₁ hb_in)
                have ⟨hl₄,hr₄⟩ := href₄
                have hdb := (hr₄ hopen_in)
                have ⟨_,hb_out⟩ := hdb
                assumption

/- The initialisation of the tank -/
def Tank1.init : InitEvent (Tank1 ctx) Unit Unit :=
    {
        init := fun _ _ => ((),{ cpt := 0 , st := status.CLOSED})
        guard _ := True
    }

/- which is a safe init Event-/
instance inst1 : SafeInitEvent (Tank1.init (ctx:= ctx)) where
    safety m _ := by simp[Machine.invariant,Tank1.init]


/- and also a refinement of the initialisation of the counter -/
instance : SafeInitREvent (Tank1.init (ctx:= ctx)) (Counter0.Init (ctx:= ctx)) where
    lift_in := id
    lift_out := id
    strengthening := by simp[Tank1.init,Counter0.Init]
    simulation :=  by simp[Refinement.refine, Tank1.init, Counter0.Init]

/- and a refinement of the initialisation of the xor-/
instance : SafeInitREvent (Tank1.init (ctx:= ctx)) (Xor0.Init (ctx:= ctx')) where
    lift_in := id
    lift_out := id
    strengthening := by simp[Tank1.init,Xor0.Init]
    simulation :=  by simp[Refinement.refine, Tank1.init, Xor0.Init]


/- First event : filling up the tank, without touching the doors-/
def Tank1.fill : Event (Tank1 ctx) Nat Unit :=
  {
    kind := EventKind.TransDet (Convergence.Ordinary)
    action := fun t1 v _ => ((),
        {   cpt:= t1.cpt + v,
            st := t1.st
        })
    guard := fun t1 v => (t1.st = status.OPEN_IN) ∧ (t1.cpt + v < ctx.max)
  }

/- it is a SafeEvent -/
instance : SafeEvent (Tank1.fill (ctx:=ctx))  where
    safety := fun m v =>
        by
            simp[Machine.invariant, Tank1.fill]
            omega

/- It refines the Incr event of the counter -/
instance : SafeREvent   (Tank1.fill (ctx := ctx)) (Counter0.Incr (ctx :=ctx))
    (valid_kind :=
        by
            simp[EventKind.refine?,Tank1.fill,Counter0.Incr]
    )
    where
    lift_in := id
    lift_out := id
    strengthening :=
        fun m x =>
            by
                simp[Machine.invariant,Counter0.Incr,Refinement.refine,Tank1.fill]
                intros _ _ _ _ href
                rw[href]
                omega
    simulation :=
        fun m x =>
            by
                simp[Machine.invariant,Counter0.Incr,Refinement.refine,Tank1.fill]

/- As we don't modify the status of the door, it refines the skip event of the Xor machine -/
instance : SafeREvent (Tank1.fill (ctx := ctx)) (skip_Event (Xor0 ctx₀) Unit)
    (valid_kind :=
        by simp[EventKind.refine?,Tank1.fill]
    ) where
    lift_in := fun _ => ()
    lift_out := id
    strengthening :=
        fun m x => by simp
    simulation :=
        fun m x =>
            by
                simp[Machine.invariant, Refinement.refine,Tank1.fill]

/- Second event : filling up the tank to its maximum capacity and automatically closing the door -/

def Tank1.fillUp : Event (Tank1 ctx) Nat Unit :=
    {
        kind := EventKind.TransDet (Convergence.Ordinary)
        action _ _ _ :=
        ((),
            {
                cpt := ctx.max,
                st := status.CLOSED
            }
        )
        guard t1 v := t1.cpt + v = ctx.max ∧  t1.st = status.OPEN_IN
    }

/- It is a SafeEvent -/
instance : SafeEvent (Tank1.fillUp (ctx :=ctx))  where
    safety m _ := by simp[Machine.invariant,Tank1.fillUp]

/- It refines the Incr event of the counter -/
instance : SafeREvent (Tank1.fillUp (ctx := ctx)) (Counter0.Incr (ctx:= ctx))
    (valid_kind := by simp[EventKind.refine?,Tank1.fillUp,Counter0.Incr])
    where
    lift_in := id
    lift_out := id
    strengthening m x:=
        by
            simp[Machine.invariant,Refinement.refine, Counter0.Incr,Tank1.fillUp]
            intros hinv₁ hgrd₁ hgrd₂ am href
            rw[href]
            simp[hgrd₁]
    simulation m x :=
        by
            simp[Machine.invariant,Refinement.refine, Counter0.Incr,Tank1.fillUp]
            intros hinv₁ hgrd₁ hgrd₂ am href
            rw[href]
            assumption

/- It also refines the event SetX_false of the Xor -/
instance : SafeREvent
     (Tank1.fillUp (ctx:= ctx)) (Xor0.SetX_false (ctx:= ctx'))
     (valid_kind := by simp[EventKind.refine?,Tank1.fillUp,Xor0.SetX_false])
    where
    lift_in := fun _ => ()
    lift_out := id
    strengthening m x := by simp[Xor0.SetX_false]
    simulation m x :=
        by
            simp[Machine.invariant,Refinement.refine,Tank1.fillUp,Xor0.SetX_false]
            intros hinv₁ hgrd₁ hgrd₂ am href₁ href₂ href₃ href₄ href₅
            simp[hgrd₂] at href₄
            exact href₄.2


/- -/
def Tank1.drain : Event (Tank1 ctx) Nat Unit :=
    {
        kind := EventKind.TransDet (Convergence.Ordinary)
        action m v _ := ((),{cpt := m.cpt - v, st := m.st})
        guard m v := m.st = status.OPEN_OUT ∧ m.cpt - v > 0
    }

instance : SafeEvent (Tank1.drain (ctx:=ctx))  where
    safety m v :=
    by
        simp[Machine.invariant,Tank1.drain]
        omega

instance : SafeREvent
    (Tank1.drain (ctx:= ctx)) (Counter0.Decr (ctx:=ctx))
    (valid_kind := by simp[EventKind.refine?,Tank1.drain,Counter0.Decr])
    where
    lift_in := id
    lift_out := id
    strengthening := by
        simp[Machine.invariant,Refinement.refine,Tank1.drain, Counter0.Decr]
    simulation m x :=
        by
            simp[Machine.invariant, Refinement.refine, Tank1.drain, Counter0.Decr]
            intros hinv hgrd₁ hgrd₂ am href
            rw[href]

instance : SafeREvent
    (Tank1.drain (ctx:= ctx)) (skip_Event (Xor0 ctx₀) Unit)
    (valid_kind := by simp[EventKind.refine?,Tank1.drain])
    where
    lift_in := fun _ => ()
    lift_out := id
    strengthening m x := by simp[Machine.invariant, Refinement.refine]
    simulation := by simp[Machine.invariant,Refinement.refine, Tank1.drain]



def Tank1.drainAll : Event (Tank1 ctx) Unit Unit :=
    {
        kind := EventKind.TransDet (Convergence.Ordinary)
        action _ _ _ := ((), {cpt :=0,st:= status.CLOSED})
        guard m _ := m.st = status.OPEN_OUT
    }


instance : SafeEvent (Tank1.drainAll (ctx := ctx))  where
    safety := by simp[Machine.invariant,Tank1.drainAll]

instance : SafeREvent
    (Tank1.drainAll (ctx:=ctx)) (Counter0.Decr (ctx:=ctx))
    (valid_kind := by simp[EventKind.refine?,Tank1.drainAll,Counter0.Decr])
    where
    lift_in := fun _ => ctx.max -- litte trick : it works because with nats, if x ≤ y, x - y = 0
    lift_out := id
    strengthening := by simp[Machine.invariant,Refinement.refine,Counter0.Decr,Tank1.drainAll]
    simulation :=
        by
            simp[Machine.invariant,Refinement.refine, Counter0.Decr,Tank1.drainAll]
            intros m Hinv hgrd am href
            rw[href]
            omega

instance : SafeREvent (Tank1.drainAll (ctx := ctx)) (Xor0.SetY_false (ctx:=ctx'))
    (valid_kind := by simp[EventKind.refine?,Tank1.drainAll,Xor0.SetY_false])
    where
    lift_in := id
    lift_out := id
    strengthening :=
        by
            simp[Machine.invariant,Refinement.refine,Xor0.SetY_false,Tank1.drainAll]
            intros m hinv hgrd am href₁ href₂ href₃ href₄ href₅
            simp[hgrd] at href₅
            exact (href₅.1)
    simulation :=
        by
            simp[Machine.invariant,Refinement.refine,Xor0.SetY_false,Tank1.drainAll]
            intros m hinv hgrd am href₁ href₂ href₃ href₄ href₅
            simp[hgrd] at href₅
            exact (href₅.1)


def Tank1.Open_Door_in : Event (Tank1 ctx) Unit Unit :=
    {
        kind := EventKind.TransDet (Convergence.Ordinary)
        action m _ _ := ((), {cpt := m.cpt, st := status.OPEN_IN})
        guard m _ := m.st ≠ status.OPEN_OUT
    }

instance : SafeEvent (Tank1.Open_Door_in (ctx:= ctx))  where
    safety :=
        by
            simp[Machine.invariant,Tank1.Open_Door_in]
            intros m hgrd₁ _
            assumption

instance : SafeREvent (Tank1.Open_Door_in (ctx := ctx)) (skip_Event (Counter0 ctx) Unit)
    (valid_kind := by simp[EventKind.refine?, Tank1.Open_Door_in])
    where
    lift_in := id
    lift_out := id
    strengthening m x:= by simp
    simulation := by simp[Machine.invariant,Refinement.refine,Tank1.Open_Door_in]

instance : SafeREvent (Tank1.Open_Door_in (ctx:= ctx)) (Xor0.SetX_true (ctx:= ctx'))
    (valid_kind := by simp[EventKind.refine?,Tank1.Open_Door_in,Xor0.SetX_true])
    where
    lift_in := id
    lift_out := id
    strengthening m x :=
        by
            simp[Refinement.refine,Tank1.Open_Door_in,Xor0.SetX_true]
            intros hinv hgrd
            simp[hgrd]
            intros
            assumption
    simulation m x :=
        by
            simp[Machine.invariant,Refinement.refine,Tank1.Open_Door_in,Xor0.SetX_true]
            intros hinv hgrd
            simp[hgrd]
            intros
            assumption

def Tank1.Close_Door_in : Event (Tank1 ctx) Unit Unit :=
    {
        kind := EventKind.TransDet (Convergence.Ordinary)
        action m _ _ := ((),{cpt:= m.cpt, st := status.CLOSED})
        guard m _ := m.st = status.OPEN_IN
    }

instance : SafeEvent (Tank1.Close_Door_in (ctx:= ctx))  where
    safety m x :=
        by
            simp[Machine.invariant,Tank1.Close_Door_in]
            intros
            assumption

instance : SafeREvent (Tank1.Close_Door_in (ctx := ctx)) (skip_Event (Counter0 ctx) Unit)
    (valid_kind := by simp[EventKind.refine?,Tank1.Close_Door_in]) where
    lift_in := id
    lift_out := id
    strengthening m x:= by simp
    simulation := by simp[Machine.invariant,Refinement.refine,Tank1.Close_Door_in]

instance : SafeREvent (Tank1.Close_Door_in (ctx:= ctx)) (Xor0.SetX_false (ctx:= ctx'))
    (valid_kind := by simp[EventKind.refine?,Tank1.Close_Door_in, Xor0.SetX_false])
    where
    lift_in := id
    lift_out := id
    strengthening m x :=
        by
            simp[Refinement.refine,Tank1.Close_Door_in,Xor0.SetX_false]
    simulation m x :=
        by
            simp[Machine.invariant,Refinement.refine,Tank1.Close_Door_in,Xor0.SetX_false]
            intros hinv hgrd
            simp[hgrd]
            intros
            assumption



def Tank1.Open_Door_out : Event (Tank1 ctx) Unit Unit :=
    {
        kind := EventKind.TransDet (Convergence.Ordinary)
        action m _ _ := ((), {cpt := m.cpt, st := status.OPEN_OUT})
        guard m _ := m.st ≠ status.OPEN_IN
    }

instance : SafeEvent (Tank1.Open_Door_out (ctx:= ctx))  where
    safety :=
        by
            simp[Machine.invariant,Tank1.Open_Door_out]
            intros m hgrd₁ _
            assumption

instance : SafeREvent (Tank1.Open_Door_out (ctx := ctx)) (skip_Event (Counter0 ctx) Unit)
    (valid_kind := by simp[EventKind.refine?,Tank1.Open_Door_out])
    where
    lift_in := id
    lift_out := id
    strengthening m x:= by simp
    simulation := by simp[Machine.invariant,Refinement.refine,Tank1.Open_Door_out]

instance : SafeREvent (Tank1.Open_Door_out (ctx:= ctx)) (Xor0.SetY_true (ctx:= ctx'))
    (valid_kind := by simp[EventKind.refine?,Tank1.Open_Door_out,Xor0.SetY_true])
    where
    lift_in := id
    lift_out := id
    strengthening m x :=
        by
            simp[Refinement.refine,Tank1.Open_Door_out,Xor0.SetY_true]
            intros hinv hgrd
            simp[hgrd]
            intros
            assumption
    simulation m x :=
        by
            simp[Machine.invariant,Refinement.refine,Tank1.Open_Door_out,Xor0.SetY_true]
            intros hinv hgrd
            simp[hgrd]
            intros
            assumption

def Tank1.Close_Door_out : Event (Tank1 ctx) Unit Unit :=
    {
        kind := EventKind.TransDet (Convergence.Ordinary)
        action m _ _ := ((),{cpt:= m.cpt, st := status.CLOSED})
        guard m _ := m.st = status.OPEN_OUT
    }

instance : SafeEvent (Tank1.Close_Door_out (ctx:= ctx))  where
    safety m x :=
        by
            simp[Machine.invariant,Tank1.Close_Door_out]
            intros
            assumption

instance : SafeREvent (Tank1.Close_Door_out (ctx := ctx)) (skip_Event (Counter0 ctx) Unit)
    (valid_kind := by simp[EventKind.refine?,Tank1.Close_Door_out])

    where
    lift_in := id
    lift_out := id
    strengthening m x:= by simp
    simulation := by simp[Machine.invariant,Refinement.refine,Tank1.Close_Door_out]

instance : SafeREvent (Tank1.Close_Door_out (ctx:= ctx)) (Xor0.SetY_false (ctx:= ctx'))
    (valid_kind := by simp[EventKind.refine?,Tank1.Close_Door_out, Xor0.SetY_false])

    where
    lift_in := id
    lift_out := id
    strengthening m x :=
        by
            simp[Refinement.refine,Tank1.Close_Door_out,Xor0.SetY_false]
            intros _ hgrd
            simp[hgrd]
            intros
            assumption
    simulation m x :=
        by
            simp[Machine.invariant,Refinement.refine,Tank1.Close_Door_out,Xor0.SetY_false]
            intros hinv hgrd
            simp[hgrd]
            intros
            assumption
