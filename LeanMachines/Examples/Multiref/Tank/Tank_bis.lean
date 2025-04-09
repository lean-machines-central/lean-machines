import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary
import LeanMachines.Refinement.Relational.Basic
import LeanMachines.Refinement.Relational.Convergent
import LeanMachines.Refinement.Relational.Ordinary
import LeanMachines.Refinement.Relational.Multi
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


/- Init -/

def Tank1.Init :
  MultiInitREvent (Counter0 ctx) (Xor0 ctx') (Tank1 ctx) (Counter0.Init) (Xor0.Init) Unit Unit  :=
  newMultiInitREvent''
  {
    init := sorry
    safety := sorry
    ref₁ := sorry
    ref₂ := sorry
  }

def Tank1.fill :
  MultiOrdinaryREvent (Counter0 ctx) (Xor0 ctx')
  (Counter0.Incr.toOrdinaryEvent) (mkOrdinaryEvent (skip_Event (Xor0 ctx') Unit))
  (Tank1 ctx) Nat Unit
   :=
  newMultiOrdinaryREvent'
  {
    action := sorry
    safety := sorry
    ref₁ := {
      lift_in := sorry
      strengthening := sorry
      simulation := sorry
    }
    ref₂ := {
      lift_in := sorry
      strengthening := sorry
      simulation := sorry
    }
  }
