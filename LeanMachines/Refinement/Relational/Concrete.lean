import LeanMachines.Event.Ordinary
import LeanMachines.Event.Convergent
import LeanMachines.NonDet.Basic
import LeanMachines.Refinement.Relational.Basic
import LeanMachines.Refinement.Relational.Ordinary
-- import LeanMachines.Refinement.Relational.NonDet.Det.Convergent

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
convergence (which, thanks to anticipation, can be postponed to
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
