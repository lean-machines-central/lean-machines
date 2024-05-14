
import EventSystems.Refinement.Functional.Basic

open Refinement
open FRefinement

class SRefinement {ACTX : outParam (Type u₁)} (AM)
                 {CTX : outParam (Type u₂)} (M)
                 [Machine ACTX AM] [Machine CTX M] extends FRefinement AM M where

  unlift (m : M) (am' : AM): M

  lift_unlift (m : M) (am' : AM):
    Machine.invariant m → Machine.invariant am'
    → lift (unlift m am') = am'

open Refinement
open SRefinement

theorem unlift_refine  [Machine ACTX AM] [Machine CTX M] [instSR:SRefinement AM M]
  {m : M} {am : AM} (Hsafe: Machine.invariant m
                            → Machine.invariant am
                            → Machine.invariant (unlift m am)):
  Machine.invariant m → Machine.invariant am
  → refine am (unlift m am) :=
by
  intros Hinv₁ Hinv₂
  have Hinv₃ : Machine.invariant (unlift m am) := by
    exact Hsafe Hinv₁ Hinv₂

  have Href: refine (lift (unlift m am)) (unlift m am) := by
    apply lift_ref (self:=instSR.toFRefinement)
    assumption

  rw [lift_unlift] at Href <;> assumption

@[simp]
def newSREvent [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryEvent AM α' β') (ev : FREventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs.to_Event) : OrdinaryREvent AM M α β α' β' :=
  newREvent abs ev.toREventSpec

/- Initialization events -/

@[simp]
def newInitSREvent [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : InitEvent AM α' β') (ev : InitFREventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : InitREvent AM M α β α' β' :=
  newInitREvent abs ev.toInitREventSpec
