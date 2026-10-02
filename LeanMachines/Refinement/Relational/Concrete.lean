import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary
import LeanMachines.Event.Convergent
import LeanMachines.NonDet.Basic
import LeanMachines.NonDet.Ordinary
import LeanMachines.Refinement.Relational.Basic
import LeanMachines.Refinement.Relational.Ordinary
import LeanMachines.Refinement.Relational.NonDet.Det.Convergent

/-!

# Defining new, concrete events

Concrete events are events only available at the concrete level
when defining a refined machine.

Concrete events refine the (non-deterministic) `skip` event.

(the discussion below can be safely skipped)

If compared to the Event-B notion of a concrete event, there
is an important difference since we do not enforce the anticipation
or convergence of concrete events.  Of course, anticipation or
convergence or concrete event is a possible requirement, only
not mandatory.

The argument in favor of convergence is that the abstract skip
event cannot be infinitely triggered if the concrete event is
convergent (which, thanks to anticipation, can be postponed to
a further refinement).  The main counter-argument, which is the
reason why this is not enforced in LeanMachines, is that a concrete
event may not be able to define an interesting, and varying variant.
In our opinion, this is more related to a *fairness* argument
(at the abstract level), which may or may not be a desirable
requirement.

-/

open Refinement

/-!
## Concrete ordinary events
-/


/-- The specification of a concrete (ordinary) event, refining (non-deterministic) Skip.-/
structure ConcreteREvent (AM) [instAM: Machine ACTX AM]
                             (M) [instM: Machine CTX M]
                            [instR: Refinement AM M] (α) (β)
          extends OrdinaryEvent M α β where

  /-- Proof obligation: the refined event safely simulates the non-deterministic Skip event
   (no state change at the abstract level). -/
  simulation (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ am, refine (self:=instR) am m
      →  refine (self:=instR) am (action m x grd).2

#check skip_NDEvent
#check instSafeNDEventPO_Ordinary

instance [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : ConcreteREvent AM M α β):
  SafeRDetEventPO
    (ev.toEvent) (skip_NDEvent.toNDEvent)
    (instSafeAbs := instSafeNDEventPO_Ordinary (skip_NDEvent (M := AM) (α := Unit)))
    (instSafeEv := instSafeEventPO_OrdinaryEvent ev.toOrdinaryEvent)
    (valid_kind := by simp)
  where
    lift_in := fun _ => ()
    lift_out := fun _ => ()
    strengthening := sorry
    simulation m x hinv hgrd am href := by
      simp only [skip_NDEvent, OrdinaryEvent.toEvent, exists_eq_left]
      exact ev.simulation m x hinv hgrd am href

/-- The construction of a concrete (ordinary) event from a `ConcreteREventSpec` specification. -/
@[simp]
def newConcreteREvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   (ev : ConcreteREvent AM M α β) : OrdinaryRDetEvent AM M α β Unit Unit skip_NDEvent :=
  {
    action := ev.action
    safety := ev.safety
    lift_in := fun _ => ()
    lift_out := fun _ => ()
    strengthening _ _ _ _ _ _:= trivial
    simulation m x hinv hgrd am href := by
      simp only [skip_NDEvent, exists_eq_left]
      exact ev.simulation m x hinv hgrd am href
  }


/-- Variant of `ConcreteREventSpec` with implicit `Unit` output type -/
structure ConcreteREvent' (AM) [instAM: Machine ACTX AM]
                             (M) [instM: Machine CTX M]
                            [instR: Refinement AM M] (α)
          extends OrdinaryEvent' M α where

  simulation (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ am, refine (self:=instR) am m
      →  refine (self:=instR) am (action m x grd)


instance [Machine CTX M] [Machine ACTX AM] [Refinement AM M] :
  Coe (ConcreteREvent' AM M α) (ConcreteREvent  AM M  α Unit) where
  coe ev := {
              simulation := ev.simulation
              guard := ev.guard
              action m x grd := ((),ev.action m x grd)
              safety := ev.safety
            }
/-- Variant of `newConcreteREvent` with implicit `Unit` output type -/

@[simp]
def newConcreteREvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : ConcreteREvent' AM M α) : OrdinaryRDetEvent AM M α Unit Unit Unit skip_NDEvent :=
  newConcreteREvent ev



/-- Variant of `ConcreteREventSpec` with implicit `Unit` input/output type -/
structure ConcreteREvent'' (AM) [instAM: Machine ACTX AM]
                             (M) [instM: Machine CTX M]
                            [instR: Refinement AM M]
          extends OrdinaryEvent'' M  where

  simulation (m : M) :
    Machine.invariant m
    → (grd : guard m)
    → ∀ am, refine (self:=instR) am m
      →  refine (self:=instR) am (action m grd)


instance [Machine CTX M] [Machine ACTX AM] [Refinement AM M] :
  Coe (ConcreteREvent'' AM M) (ConcreteREvent  AM M  Unit Unit) where
  coe ev := {
              simulation m _ := ev.simulation m
              guard m _ := ev.guard m
              action m _ grd := ((),ev.action m grd)
              safety m _ := ev.safety m
            }
/-- Variant of `newConcreteREvent` with implicit `Unit` output type -/

@[simp]
def newConcreteREvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : ConcreteREvent'' AM M) : OrdinaryRDetEvent AM M Unit Unit Unit Unit skip_NDEvent :=
  newConcreteREvent ev
