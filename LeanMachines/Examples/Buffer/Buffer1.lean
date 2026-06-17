import Mathlib.Tactic

import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary
import LeanMachines.Event.Convergent
import LeanMachines.NonDet.Ordinary
import LeanMachines.Refinement.Relational.Basic
import LeanMachines.Refinement.Relational.Ordinary

import LeanMachines.Examples.Buffer.Buffer0


namespace Buffer


/-- The state of the abstract machine -/
structure B1 (ctx : BufContext) (α : Type) where
  /-- The buffer represented as a list -/
  buf : List α

/-- The instantiation of the machine -/
instance: Machine BufContext (B1 ctx α) where
  context := ctx
  invariant b1 := (List.length b1.buf) ≤ ctx.maxSize

instance : Refinement (B0 ctx) (B1 ctx α) where
  refine b0 b1 := b0.size = List.length b1.buf
  refine_safe am m :=
  by
    simp only [Machine.invariant]
    intros Hinv Href
    rw[Href]
    exact Hinv


/-- Initialization event (no parameter, empty buffer)-/
def B1.Init : SafeInitREvent (B0 ctx) (B1 ctx α) B0.Init Unit Unit :=
  {
    init _ _ := ((),{buf := []})
    safety _ _ :=
    by
      simp only [Machine.invariant,List.length]
      exact Nat.zero_le ctx.maxSize
    lift_in := id
    lift_out := id
    strengthening _ _ := trivial
    simulation _ _ :=
    by
      simp[Refinement.refine]
      simp[B0.Init]
  }


def B1.Put : OrdinaryREvent (B0 ctx) (B1 ctx α) B0.Put α Unit :=
{
  guard b1 _ := b1.buf.length < ctx.maxSize
  action b1 x _ := ((),{buf := x :: b1.buf })
  safety b1 x :=
  by
    simp[Machine.invariant]
    intros hinv hgrd
    exact hgrd
  lift_in := λ _ => ()
  lift_out := id
  strengthening m x :=
  by
    simp [Refinement.refine, B0.Put]
    intros hinv hgrd am href
    rw[href]
    exact hgrd
  simulation m x :=
  by
    simp only [Refinement.refine, B0.Put]
    intros hinv hgrd am href
    constructor
    · trivial
    · simp
      exact href
}
