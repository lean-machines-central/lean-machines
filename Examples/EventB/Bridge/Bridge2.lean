
import Mathlib.Tactic

import EventSystems.Refinement.Basic
import EventSystems.Refinement.Convergent

import Examples.EventB.Bridge.Bridge1

namespace BridgeSpec

inductive Color := | Green | Red
  deriving Repr, BEq, DecidableEq

structure Bridge2 (ctx : Context) extends (Bridge1 ctx) where
  mainlandTL : Color
  mainlandPass : Bool
  islandTL : Color
  islandPass : Bool

def Bridge2.invariant₁ (b : Bridge2 ctx) :=
  b.mainlandTL = Color.Green
  →  b.toBridge1.nbToIsland + b.toBridge1.nbOnIsland < ctx.maxCars
     ∧ b.toBridge1.nbFromIsland = 0

def Bridge2.invariant₂ (b : Bridge2 ctx) :=
  b.islandTL = Color.Green
  → b.nbOnIsland > 0 ∧ b.nbToIsland = 0

def Bridge2.invariant₃ (b : Bridge2 ctx) :=
  b.islandTL = Color.Red ∨ b.mainlandTL = Color.Red

def Bridge2.invariant₄ (b : Bridge2 ctx) :=
  b.mainlandTL = Color.Red → b.mainlandPass = true

def Bridge2.invariant₅ (b : Bridge2 ctx) :=
  b.islandTL = Color.Red → b.islandPass = true

def Bridge2.refine (b1 : Bridge1 ctx) (b2 : Bridge2 ctx) :=
  b2.toBridge1 = b1 -- this is a superposition

instance: Machine Context (Bridge2 ctx) where
  context := ctx
  invariant b := Bridge2.invariant₁ b ∧ Bridge2.invariant₂ b ∧ Bridge2.invariant₃ b
                 ∧ Bridge2.invariant₄ b ∧ Bridge2.invariant₅ b
                 ∧ Machine.invariant b.toBridge1
                   -- this is handy in case of superposition, insteand of putting the
                   -- glue in the refine predicate
  reset := let r1 : Bridge1 ctx := Machine.reset
           { r1 with mainlandTL := Color.Red
                     mainlandPass := false
                     islandTL := Color.Red
                     islandPass := false }

theorem Bridge2.abstract_inv (b : Bridge2 ctx):
  Machine.invariant b → Machine.invariant b.toBridge1 :=
by
  simp [Machine.invariant]

theorem Bridge2.abstract_ref (b : Bridge2 ctx):
  Machine.invariant b → refine b b.toBridge1 :=
by
  simp [refine]


instance: Refinement (Bridge1 ctx) (Bridge2 ctx) where
  refine := Bridge2.refine
  refine_safe := fun b1 b2 => by simp [Bridge2.refine] -- trivial in case of superposition
                                 intros Hinv Href
                                 simp [Machine.invariant] at *
                                 simp [←Href, Hinv]
  refine_reset am := by simp [Machine.reset, Bridge2.refine]
                        intro H ; simp [H]

namespace Bridge2

theorem refine_uniq (b2 : Bridge2 ctx) (b1a b1b : Bridge1 ctx):
    Machine.invariant b2
    → refine b1a b2 → refine b1b b2
    → b1a = b1b :=
by
  simp [Bridge2.refine]
  intros _ Href Href'
  rw [←Href, ←Href']

def Init : OrdinaryREvent (Bridge1 ctx) (Bridge2 ctx) Unit Unit :=
  newInitREvent'' {
    init := let b1 : Bridge1 ctx := Bridge1.Init.init ()
            { b1  with mainlandTL := Color.Green , islandTL := Color.Red,
                       mainlandPass := false, islandPass := true }
    safety := by simp [Machine.invariant, invariant₁, invariant₂, invariant₃, invariant₄, invariant₅]
                 simp [Bridge1.Init]
                 simp [ctx.maxCars_pos]
    abstract := Bridge1.Init.toInitEvent
    strengthening := by simp [Bridge1.Init, newInitEvent']
    simulation := by simp [Bridge1.Init, newInitEvent', Refinement.refine, Bridge2.refine, Machine.invariant]
  }

def EnterFromMainland₁ : REvent (Bridge1 ctx) (Bridge2 ctx) Unit Unit :=
  newREvent' {
    guard := fun b2 => b2.mainlandTL = Color.Green ∧ b2.nbOnIsland + b2.nbToIsland + 1 ≠ ctx.maxCars

    action := fun b2 => { b2 with nbToIsland := b2.nbToIsland + 1
                                  mainlandPass := true }
    safety := fun b2 => by simp [Machine.invariant, invariant₁, invariant₂, invariant₃, invariant₄, invariant₅]
                           intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hinv₆ Hinv₇ Hgrd₁ Hgrd₂
                           simp [Hgrd₁] at *
                           simp [Hinv₃] at *
                           simp [Hinv₅]
                           cases Hinv₁
                           case intro Hinv₁ Hinv₁' =>
                             simp [Hinv₁'] at *

                             have Hleft: b2.nbToIsland + 1 + b2.nbOnIsland < ctx.maxCars := by
                               have H₁ : b2.nbToIsland + 1 + b2.nbOnIsland
                                         = b2.nbToIsland + b2.nbOnIsland + 1 := by simp_arith
                               rw [H₁] ; clear H₁
                               apply Nat.lt_of_le_of_ne
                               · exact Hinv₁
                               · conv => pattern b2.nbToIsland + b2.nbOnIsland
                                         rw [Nat.add_comm]
                                 exact Hgrd₂
                             simp [Hleft]
                             exact Nat.le_of_lt Hleft

    abstract := Bridge1.EnterFromMainland.toEvent

    strengthening := fun b2 => by simp [Bridge1.EnterFromMainland, Refinement.refine, Bridge2.refine, Machine.invariant, invariant₁, invariant₂, invariant₃, invariant₄, invariant₅]
                                  intros Hinv₁ _ Hinv₃ _ _ _ _ Hgrd₁ _
                                  simp [Hgrd₁, Hinv₃, Hinv₁]

    simulation := fun b2 => by simp [Machine.invariant, Refinement.refine, Bridge2.refine, Bridge1.EnterFromMainland]

    abstract_ok := by simp [Bridge1.EnterFromMainland, Bridge0.EnterFromMainland, newEvent']
  }

def EnterFromMainland₂ : REvent (Bridge1 ctx) (Bridge2 ctx) Unit Unit :=
  newREvent' {
    guard := fun b2 => b2.mainlandTL = Color.Green ∧ b2.nbOnIsland + b2.nbToIsland + 1 = ctx.maxCars
    action := fun b2 => { b2 with nbToIsland := b2.nbToIsland + 1
                                  mainlandTL := Color.Red
                                  mainlandPass := true }

    safety := fun b2 => by simp [Machine.invariant, invariant₁, invariant₂, invariant₃, invariant₄, invariant₅]
                           intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hinv₆ Hinv₇ Hgrd₁ Hgrd₂
                           simp [Hgrd₁] at *
                           simp [Hinv₃, Hinv₅, Hinv₁] at *
                           rw [←Hgrd₂]
                           simp_arith

    abstract := Bridge1.EnterFromMainland.toEvent

    strengthening := fun b2 => by simp [Bridge1.EnterFromMainland, Refinement.refine, Bridge2.refine, Machine.invariant, invariant₁, invariant₂, invariant₃, invariant₄, invariant₅]
                                  intros Hinv₁ _ Hinv₃ _ _ _ _ Hgrd₁ _
                                  simp [Hgrd₁, Hinv₃, Hinv₁]

    simulation := fun b2 => by simp [Machine.invariant, Refinement.refine, Bridge2.refine, Bridge1.EnterFromMainland, invariant₁, invariant₂, invariant₃, invariant₄, invariant₅]

    abstract_ok := by simp [Bridge1.EnterFromMainland, Bridge0.EnterFromMainland, newEvent']
  }

def LeaveToMainland : REvent (Bridge1 ctx) (Bridge2 ctx) Unit Unit :=
  newAbstractREvent {
    event := Bridge1.LeaveToMainland.toEvent
    lift := fun b2 _ => b2.toBridge1
    lift_ref := fun b2 => by simp [Refinement.refine, refine]
    refine_uniq := fun b2 b1a b1b => by apply refine_uniq
    unlift := fun b2 _ b1' _=> { b2 with toBridge1 := b1' }
    lift_unlift := fun b2 _ => by simp
    step_ref := fun b2 x => by simp [Refinement.refine, refine]
    step_inv := fun b2 x =>   by simp
                                 intros Hinv Hgrd
                                 have Hainv := Refinement.refine_inv b2 b2.toBridge1 Hinv rfl
                                 have Hsafe:= Bridge1.LeaveToMainland.toEvent.safety b2.toBridge1 x Hainv Hgrd
                                 simp [Bridge1.LeaveToMainland, Machine.invariant
                                      , invariant₁, invariant₂, invariant₃, invariant₄, invariant₅] at *
                                 obtain ⟨Hinv₁, Hinv₂, Hinv₃, Hinv₄, Hinv₅, Hinv₆⟩ := Hinv
                                 simp [*] at *
                                 cases Hinv₃
                                 case inl Hinv₃ =>
                                   simp [*] at *
                                   have Hcut: b2.mainlandTL = Color.Green ∨ b2.mainlandTL = Color.Red := by
                                     cases b2.mainlandTL <;> trivial
                                   cases Hcut <;> simp [*]
                                 case inr Hinv₃ =>
                                   simp [*] at *
                                   have Hcut: b2.islandTL = Color.Green ∨ b2.islandTL = Color.Red := by
                                     cases b2.islandTL <;> trivial
                                   cases Hcut <;> simp [*]

    event_ok := by simp [Bridge1.LeaveToMainland, Bridge0.LeaveToMainland, newEvent']
  }

def EnterIsland : RConvergentEvent Nat (Bridge1 ctx) (Bridge2 ctx) Unit Unit :=
  newAbstractRConvergentEvent Nat {
    event := Bridge1.EnterIsland.toEvent
    lift := fun b2 _ => b2.toBridge1
    lift_ref := fun b2 => by simp [Refinement.refine, refine]
    refine_uniq := fun b2 b1a b1b => by apply refine_uniq
    unlift := fun b2 _ b1' _ => { b2 with toBridge1 := b1' }
    lift_unlift := fun b2 _ => by simp
    step_ref := fun b2 x => by simp [Refinement.refine, refine]
    step_inv := fun b2 x =>   by simp
                                 intros Hinv Hgrd
                                 have Hainv := Refinement.refine_inv b2 b2.toBridge1 Hinv rfl
                                 have Hsafe:= Bridge1.EnterIsland.toEvent.safety b2.toBridge1 x Hainv Hgrd
                                 simp [Bridge1.EnterIsland, newConcreteREvent', Machine.invariant
                                      , invariant₁, invariant₂, invariant₃, invariant₄, invariant₅] at *
                                 obtain ⟨Hinv₁, Hinv₂, Hinv₃, Hinv₄, Hinv₅, Hinv₆⟩ := Hinv
                                 simp [*] at *
                                 cases Hinv₃
                                 case inl Hinv₃ =>
                                   simp [*] at *
                                   have Hcut: b2.mainlandTL = Color.Green ∨ b2.mainlandTL = Color.Red := by
                                     cases b2.mainlandTL <;> trivial
                                   cases Hcut
                                   case inl Hcut =>
                                     simp [*] at *
                                     have Hcalc := by calc  b2.nbToIsland - 1 + (b2.nbOnIsland + 1) = b2.nbToIsland - 1 + 1  + b2.nbOnIsland := by simp_arith
                                                            _ =   b2.nbToIsland + b2.nbOnIsland := by rw [Nat.sub_add_cancel]
                                                                                                      exact Hgrd
                                     rw [Hcalc]
                                     simp [Hinv₁]
                                   case inr Hcut =>
                                     simp [*] at *
                                 case inr Hinv₃ =>
                                   simp [*] at *
                                   have Hcut: b2.islandTL = Color.Green ∨ b2.islandTL = Color.Red := by
                                     cases b2.islandTL <;> trivial
                                   cases Hcut
                                   case inl Hcut =>
                                     simp [*] at *
                                   case inr Hcut =>
                                     simp [*] at *

    abstract_cnv := Bridge1.EnterIsland.toConvergentEvent
    abstract_cnv_prop := by simp
    cvariant := fun b2 => Bridge1.EnterIsland.variant b2.toBridge1
    cvariant_prop := fun b2 _ => by simp
  }

def LeaveIsland₁ : RConvergentEvent Nat (Bridge1 ctx) (Bridge2 ctx) Unit Unit :=
  newRConvergentEvent' {
    guard := fun b2 => b2.islandTL = Color.Green ∧ b2.nbOnIsland ≠ 1

    action := fun b2 => { b2 with nbFromIsland := b2.nbFromIsland + 1
                                  nbOnIsland := b2.nbOnIsland - 1
                                  islandPass := true }

    safety := fun b2 => by simp [Machine.invariant, invariant₁, invariant₂, invariant₃, invariant₄, invariant₅]
                           rintro Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hinv₆ Hinv₇ Hgrd₁ Hgrd₂
                           simp [*] at *
                           have Hml: b2.mainlandTL = Color.Green ∨ b2.mainlandTL = Color.Red := by
                             cases b2.mainlandTL <;> trivial
                           cases Hml
                           case inl Hml =>
                             simp [*] at *
                           case inr Hml =>
                             simp [*] at *
                             constructor
                             · apply Nat.lt_of_le_of_ne
                               · apply Nat.le_of_pred_lt ; simp_arith [Hinv₂]
                               · exact Ne.symm Hgrd₂
                             · rw [Nat_sub_add_comm_cancel]
                               · assumption
                               · apply Nat.le_of_pred_lt ; simp_arith [Hinv₂.1]

    variant := fun b2 => Bridge1.LeaveIsland.variant b2.toBridge1

    convergence := fun b2 => by simp
                                intros Hinv Hgrd₁ _
                                simp [Bridge1.LeaveIsland, newConcreteREvent']
                                simp [Machine.invariant, invariant₂] at Hinv
                                simp [*] at *
                                simp [@tsub_lt_self_iff, Hinv]

    abstract := Bridge1.LeaveIsland.toEvent

    strengthening := fun b2 => by simp
                                  intro Hinv Hgrd₁ _
                                  simp [Refinement.refine, refine, Bridge1.LeaveIsland, newConcreteREvent']
                                  simp [Machine.invariant, invariant₂] at Hinv
                                  simp [Hinv, Hgrd₁]

    simulation := fun b2 => by simp
                               intros _ _ _ am
                               simp [Refinement.refine, refine, Bridge1.LeaveIsland, newConcreteREvent']
                               intro Href
                               simp [←Href] at *
  }

def LeaveIsland₂ : RConvergentEvent Nat (Bridge1 ctx) (Bridge2 ctx) Unit Unit :=
  newRConvergentEvent' {
    guard := fun b2 => b2.islandTL = Color.Green ∧ b2.nbOnIsland = 1

    action := fun b2 => { b2 with nbFromIsland := b2.nbFromIsland + 1
                                  nbOnIsland := b2.nbOnIsland - 1
                                  islandTL := Color.Red
                                  islandPass := true }

    safety := fun b2 => by simp [Machine.invariant, invariant₁, invariant₂, invariant₃, invariant₄, invariant₅]
                           intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hinv₆ Hinv₇ Hgrd₁ Hgrd₂
                           simp [*] at *
                           have Hml: b2.mainlandTL = Color.Green ∨ b2.mainlandTL = Color.Red := by
                             cases b2.mainlandTL <;> trivial
                           cases Hml
                           case inl Hml =>
                             simp [*] at *
                           case inr Hml =>
                             simp [*] at *
                             rw [Nat.add_comm]
                             assumption

    variant := fun b2 => Bridge1.LeaveIsland.variant b2.toBridge1

    convergence := fun b2 => by simp
                                intros Hinv _ Hgrd₂
                                simp [Bridge1.LeaveIsland, newConcreteREvent']
                                simp [Machine.invariant, invariant₂] at Hinv
                                simp [*] at *

    abstract := Bridge1.LeaveIsland.toEvent

    strengthening := fun b2 => by simp
                                  intro Hinv Hgrd₁ _
                                  simp [Refinement.refine, refine, Bridge1.LeaveIsland, newConcreteREvent']
                                  simp [Machine.invariant, invariant₂] at Hinv
                                  simp [Hinv, Hgrd₁]

    simulation := fun b2 => by simp
                               intros _ _ _ am
                               simp [Refinement.refine, refine, Bridge1.LeaveIsland, newConcreteREvent']
                               intro Href
                               simp [←Href] at *

  }

@[simp]
def bval (b : Bool) : Nat :=
  match b with
  | false => 0
  | true => 1

def MailandTLGreen : RConvergentEvent Nat (Bridge1 ctx) (Bridge2 ctx) Unit Unit :=
  newConcreteREvent' Nat {
    guard := fun b2 => b2.mainlandTL = Color.Red ∧ b2.nbToIsland + b2.nbOnIsland < ctx.maxCars ∧ b2.nbFromIsland = 0 ∧ b2.islandPass = true

    action := fun b2 => { b2 with mainlandTL := Color.Green
                                  islandTL := Color.Red
                                  mainlandPass := false }

    safety := fun b2 => by simp [Machine.invariant, invariant₁, invariant₂, invariant₃, invariant₄, invariant₅]
                           intros Hinv₁ _ Hinv₃ Hinv₄ Hinv₅ Hinv₆ Hinv₇ Hgrd₁ Hgrd₂ Hgrd₃ Hgrd₄
                           simp [*] at *
                           assumption

    variant := fun b2 => (bval b2.mainlandPass) + (bval b2.islandPass)

    convergence := fun b2 => by simp
                                intros Hinv Hgrd₁ _ _ _
                                simp [Machine.invariant, invariant₄] at Hinv
                                simp [Hgrd₁] at Hinv
                                simp [Hinv]

    simulation := fun b2 => by simp [Refinement.refine, refine]
  }

def IslandTLGreen : RConvergentEvent Nat (Bridge1 ctx) (Bridge2 ctx) Unit Unit :=
  newConcreteREvent' Nat {
    guard := fun b2 => b2.islandTL = Color.Red ∧ b2.nbOnIsland > 0 ∧ b2.nbToIsland = 0 ∧ b2.mainlandPass = true

    action := fun b2 => { b2 with mainlandTL := Color.Red
                                  islandTL := Color.Green
                                  islandPass := false }

    safety := fun b2 => by simp [Machine.invariant, invariant₁, invariant₂, invariant₃, invariant₄, invariant₅]
                           intros Hinv₁ _ Hinv₃ Hinv₄ Hinv₅ Hinv₆ Hinv₇ Hgrd₁ Hgrd₂ Hgrd₃ Hgrd₄
                           simp [*] at *
                           assumption

    variant := fun b2 => (bval b2.mainlandPass) + (bval b2.islandPass)

    convergence := fun b2 => by simp
                                intros Hinv Hgrd₁ _ _ _
                                simp [Machine.invariant, invariant₅] at Hinv
                                simp [Hgrd₁] at Hinv
                                simp [Hinv]

    simulation := fun b2 => by simp [Refinement.refine, refine]
  }

end Bridge2

end BridgeSpec
