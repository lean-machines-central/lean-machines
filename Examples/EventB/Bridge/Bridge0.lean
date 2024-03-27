
import EventSystems.Basic

namespace BridgeSpec

structure Context where
  maxCars : Nat
  maxCars_pos : maxCars > 0

structure Bridge0 (ctx : Context) where
  nbCars : Nat

instance: Machine Context (Bridge0 ctx) where
  context := ctx
  invariant m := m.nbCars ≤ ctx.maxCars
  reset := { nbCars := 0 }

namespace Bridge0

def Init : OrdinaryEvent (Bridge0 ctx) Unit Unit := newInitEvent'' {
  init := { nbCars := 0 }
  safety := by simp [Machine.invariant]
}

def EnterFromMainland : OrdinaryEvent (Bridge0 ctx) Unit Unit := newEvent'' {
  guard := fun m => m.nbCars < ctx.maxCars
  action := fun m => { nbCars := m.nbCars + 1}
  safety := fun m => by simp [Machine.invariant]
                        intros _ Hgrd
                        exact Hgrd
}

def LeaveToMainland : OrdinaryEvent (Bridge0 ctx) Unit Unit := newEvent'' {
  guard := fun m => m.nbCars > 0
  action := fun m => { nbCars := m.nbCars - 1}
  safety := fun m => by simp [Machine.invariant]
                        intros Hinv _  -- remark : 0 - 1 = 0
                        refine Nat.sub_le_of_le_add ?h
                        exact Nat.le_step Hinv
}

theorem deadlockFreedom (m : Bridge0 ctx):
  Machine.invariant m
  → EnterFromMainland.guard m () ∨ LeaveToMainland.guard m () :=
by
  simp [Machine.invariant, EnterFromMainland, LeaveToMainland, newEvent']
  intro Hinv
  have Hctx := ctx.maxCars_pos
  have Hnb : m.nbCars < ctx.maxCars ∨ m.nbCars = ctx.maxCars := by exact Nat.lt_or_eq_of_le Hinv
  cases Hnb <;> simp [*]

end Bridge0

end BridgeSpec
