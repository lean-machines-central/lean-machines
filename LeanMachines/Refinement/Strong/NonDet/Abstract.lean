
import LeanMachines.Refinement.Strong.NonDet.Basic
import LeanMachines.Refinement.Functional.NonDet.Abstract

open Refinement
open FRefinement
open SRefinement

structure AbstractSRNDEventSpec (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                            [instSR: SRefinement AM M]
  {α β} (abstract : OrdinaryNDEvent AM α β)
      where

  step_inv (m : M) (x : α):
    Machine.invariant m
    → abstract.guard (lift m) x
    → ∀ y, ∀ am', abstract.effect (lift m) x (y, am')
                  → Machine.invariant (unlift m am')

@[simp]
def AbstractSRNDEventSpec.toAbstractFRNDEventSpec  [Machine ACTX AM] [Machine CTX M] [instSR: SRefinement AM M]
  (abstract : OrdinaryNDEvent AM α β)
  (ev : AbstractSRNDEventSpec AM M abstract) : AbstractFRNDEventSpec AM M abstract :=
  {
    unlift := fun _ am' m _ => SRefinement.unlift m am'

    step_ref := fun m x => by
      simp
      intros Hinv Hgrd y am' Heff
      have Hlr := lift_ref (AM:=AM) m Hinv
      have Hsafe := refine_safe (self:=instRefinementOfFRefinement) (lift m) m Hinv Hlr
      have Hinv' := abstract.po.safety (lift m) x Hsafe Hgrd y am' Heff
      refine unlift_refine ?Hsafe Hinv Hinv'
      intros
      exact ev.step_inv m x Hinv Hgrd y am' Heff

    step_safe := fun m x => by
      simp
      intros Hinv Hgrd _ am' Heff
      exact ev.step_inv m x Hinv Hgrd _ am' Heff

    lift_unlift := fun m am am' x => by
      simp
      intros Hinv Hainv'
      apply lift_unlift (self:=instSR) m am' Hinv Hainv'
  }

@[simp]
def newAbstractSRNDEvent [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryNDEvent AM α β)
  (ev : AbstractSRNDEventSpec AM M abs) : OrdinaryRNDEvent AM M α β :=
  newAbstractFRNDEvent abs ev.toAbstractFRNDEventSpec

structure AbstractSRNDEventSpec' (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                            [instSR: SRefinement AM M]
  {α} (abstract : OrdinaryNDEvent AM α Unit)
      where

  step_inv (m : M) (x : α):
    Machine.invariant m
    → abstract.guard (lift m) x
    → ∀ am', abstract.effect (lift m) x ((), am')
             → Machine.invariant (unlift m am')

@[simp]
def AbstractSRNDEventSpec'.toAbstractSRNDEventSpec  [Machine ACTX AM] [Machine CTX M] [instSR: SRefinement AM M]
  (abstract : OrdinaryNDEvent AM α Unit)
  (ev : AbstractSRNDEventSpec' AM M abstract) : AbstractSRNDEventSpec AM M abstract :=
  {
    step_inv := fun m x => by
      intros Hinv Hgrd _ am' Heff
      apply ev.step_inv m x <;> assumption
  }

@[simp]
def newAbstractSRNDEvent' [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryNDEvent AM α Unit)
  (ev : AbstractSRNDEventSpec' AM M abs) : OrdinaryRNDEvent AM M α Unit :=
  newAbstractSRNDEvent abs ev.toAbstractSRNDEventSpec

structure AbstractSRNDEventSpec'' (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                            [instSR: SRefinement AM M]
  (abstract : OrdinaryNDEvent AM Unit Unit)
      where

  step_inv (m : M):
    Machine.invariant m
    → abstract.guard (lift m) ()
    → ∀ am', abstract.effect (lift m) () ((), am')
             → Machine.invariant (unlift m am')

@[simp]
def AbstractSRNDEventSpec''.toAbstractSRNDEventSpec  [Machine ACTX AM] [Machine CTX M] [instSR: SRefinement AM M]
  (abstract : OrdinaryNDEvent AM Unit Unit)
  (ev : AbstractSRNDEventSpec'' AM M abstract) : AbstractSRNDEventSpec AM M abstract :=
  {
    step_inv := fun m () => by
      intros Hinv Hgrd _ am' Heff
      apply ev.step_inv m <;> assumption
  }

@[simp]
def newAbstractSRNDEvent'' [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit)
  (ev : AbstractSRNDEventSpec'' AM M abs) : OrdinaryRNDEvent AM M Unit Unit :=
  newAbstractSRNDEvent abs ev.toAbstractSRNDEventSpec

structure AbstractInitSRNDEventSpec (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                            [instSR: SRefinement AM M]
  {α β} (abstract : InitNDEvent AM α β)
      where

  step_inv (x : α):
    abstract.guard x
    → ∀ y, ∀ am', abstract.init x (y, am')
                  → Machine.invariant (unlift (Machine.reset (M:=M)) am')

@[simp]
def AbstractInitSRNDEventSpec.toAbstractInitFRNDEventSpec  [Machine ACTX AM] [Machine CTX M] [instSR: SRefinement AM M]
  (abstract : InitNDEvent AM α β)
  (ev : AbstractInitSRNDEventSpec AM M abstract) : AbstractInitFRNDEventSpec AM M abstract :=
  {
    unlift := fun _ am' m _ => SRefinement.unlift m am'

    step_ref := fun x => by
      simp
      intros Hgrd y am' Heff
      have Hainv := abstract.po.safety x Hgrd y am' Heff
      have Hsi := ev.step_inv x Hgrd y am' Heff
      have Href := lift_ref (AM:=AM) (unlift Machine.reset am') Hsi
      have Hlu := lu_reset (self:=instSR) am' Hainv
      rw [Hlu] at Href
      assumption

    step_safe := fun x => by
      simp
      intros Hgrd _ am' Heff
      exact ev.step_inv x Hgrd _ am' Heff

    lift_unlift := fun am am' x => by
      simp
      apply lu_reset
      assumption
  }

@[simp]
def newAbstractInitSRNDEvent [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : InitNDEvent AM α β)
  (ev : AbstractInitSRNDEventSpec AM M abs) : InitRNDEvent AM M α β :=
  newAbstractInitFRNDEvent abs ev.toAbstractInitFRNDEventSpec

structure AbstractInitSRNDEventSpec' (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                            [instSR: SRefinement AM M]
  {α} (abstract : InitNDEvent AM α Unit)
      where

  step_inv (x : α):
    abstract.guard x
    → ∀ am', abstract.init x ((), am')
             → Machine.invariant (unlift (Machine.reset (M:=M)) am')

@[simp]
def AbstractInitSRNDEventSpec'.toAbstractInitSRNDEventSpec  [Machine ACTX AM] [Machine CTX M] [instSR: SRefinement AM M]
  (abstract : InitNDEvent AM α Unit)
  (ev : AbstractInitSRNDEventSpec' AM M abstract) : AbstractInitSRNDEventSpec AM M abstract :=
  {
    step_inv := fun x => by
      intros Hgrd _ am' Hini
      apply ev.step_inv <;> assumption
  }

@[simp]
def newAbstractInitSRNDEvent' [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : InitNDEvent AM α Unit)
  (ev : AbstractInitSRNDEventSpec' AM M abs) : InitRNDEvent AM M α Unit :=
  newAbstractInitSRNDEvent abs ev.toAbstractInitSRNDEventSpec

structure AbstractInitSRNDEventSpec'' (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                            [instSR: SRefinement AM M]
  (abstract : InitNDEvent AM Unit Unit)
      where

  step_inv:
    abstract.guard ()
    → ∀ am', abstract.init () ((), am')
             → Machine.invariant (unlift (Machine.reset (M:=M)) am')

@[simp]
def AbstractInitSRNDEventSpec''.toAbstractInitSRNDEventSpec  [Machine ACTX AM] [Machine CTX M] [instSR: SRefinement AM M]
  (abstract : InitNDEvent AM Unit Unit)
  (ev : AbstractInitSRNDEventSpec'' AM M abstract) : AbstractInitSRNDEventSpec AM M abstract :=
  {
    step_inv := fun () => by
      intros Hgrd _ am' Hini
      apply ev.step_inv <;> assumption
  }

@[simp]
def newAbstractInitSRNDEvent'' [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : InitNDEvent AM Unit Unit)
  (ev : AbstractInitSRNDEventSpec'' AM M abs) : InitRNDEvent AM M Unit Unit :=
  newAbstractInitSRNDEvent abs ev.toAbstractInitSRNDEventSpec


@[simp]
def newAbstractAnticipatedSRNDEvent [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : AnticipatedNDEvent v AM α β)
  (ev : AbstractSRNDEventSpec AM M abs.toOrdinaryNDEvent) : AnticipatedRNDEvent v AM M α β :=
  newAbstractAnticipatedFRNDEvent abs (ev.toAbstractFRNDEventSpec abs.toOrdinaryNDEvent)

@[simp]
def newAbstractAnticipatedSRNDEvent' [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : AnticipatedNDEvent v AM α Unit)
  (ev : AbstractSRNDEventSpec' AM M abs.toOrdinaryNDEvent) : AnticipatedRNDEvent v AM M α Unit :=
  newAbstractAnticipatedSRNDEvent abs ev.toAbstractSRNDEventSpec

@[simp]
def newAbstractAnticipatedSRNDEvent'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : AnticipatedNDEvent v AM Unit Unit)
  (ev : AbstractSRNDEventSpec'' AM M abs.toOrdinaryNDEvent) : AnticipatedRNDEvent v AM M Unit Unit :=
  newAbstractAnticipatedSRNDEvent abs ev.toAbstractSRNDEventSpec

@[simp]
def newAbstractConvergentSRNDEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : ConvergentNDEvent v AM α β) (ev : AbstractSRNDEventSpec AM M abs.toAnticipatedNDEvent.toOrdinaryNDEvent) : ConvergentRNDEvent v AM M α β :=
  newAbstractConvergentFRNDEvent abs (ev.toAbstractFRNDEventSpec abs.toAnticipatedNDEvent.toOrdinaryNDEvent)

@[simp]
def newAbstractConvergentSRNDEvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : ConvergentNDEvent v AM α Unit) (ev : AbstractSRNDEventSpec' AM M abs.toAnticipatedNDEvent.toOrdinaryNDEvent) : ConvergentRNDEvent v AM M α Unit :=
  newAbstractConvergentSRNDEvent abs ev.toAbstractSRNDEventSpec

@[simp]
def newAbstractConvergentSRNDEvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : ConvergentNDEvent v AM Unit Unit) (ev : AbstractSRNDEventSpec' AM M abs.toAnticipatedNDEvent.toOrdinaryNDEvent) : ConvergentRNDEvent v AM M Unit Unit :=
  newAbstractConvergentSRNDEvent abs ev.toAbstractSRNDEventSpec
