
import EventSystems.NonDet.Basic
import EventSystems.NonDet.Ordinary
import EventSystems.Refinement.Relational.Basic

open Refinement

structure _RNDEventPO  [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
   (ev : _NDEvent M α β) (kind : EventKind)
   extends _NDEventPO ev kind where

  abstract : _NDEvent AM α β

  strengthening (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → ∀ am, refine am m
      → abstract.guard am x

  simulation (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → ∀ y, ∀ m', ev.effect m x (y, m')
      → ∀ am, refine am m
        → ∃ am', abstract.effect am x (y, am')
                 ∧ refine am' m'

structure OrdinaryRNDEvent (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M] (α) (β) extends _NDEvent M α β where
  po : _RNDEventPO (instR:=instR) to_NDEvent (EventKind.TransNonDet Convergence.Ordinary)

structure RNDEventSpec (AM) [Machine ACTX AM]
                       (M) [Machine CTX M]
                      [Refinement AM M] (α) (β)
  extends NDEventSpec M α β where

  abstract : OrdinaryNDEvent AM α β

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ am, refine am m
      → abstract.guard am x

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ y, ∀ m', effect m x (y, m')
      -- XXX : some constraint on output ?
      → ∀ am, refine am m
        → ∃ am', abstract.effect am x (y, am')
                 ∧ refine am' m'

@[simp]
def newRNDEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : RNDEventSpec AM M α β) : OrdinaryRNDEvent AM M α β :=
  {
    to_NDEvent := ev.to_NDEvent
    po := { safety := fun m x => by simp
                                    intros Hinv Hgrd
                                    apply ev.safety <;> assumption
            feasibility := fun m x => by simp
                                         intros Hinv Hgrd
                                         apply ev.feasibility <;> assumption
            abstract := ev.abstract.to_NDEvent
            strengthening := ev.strengthening
            simulation := ev.simulation
    }
  }

structure RNDEventSpec' (AM) [Machine ACTX AM]
                        (M) [Machine CTX M]
                        [Refinement AM M] (α)
  extends NDEventSpec' M α where

  abstract : OrdinaryNDEvent AM α Unit

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ am, refine am m
      → abstract.guard am x

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ m', effect m x m'
      → ∀ am, refine am m
        → ∃ am', abstract.effect am x ((), am')
                 ∧ refine am' m'

def RNDEventSpec'.toRNDEventSpec [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : RNDEventSpec' AM M α) : RNDEventSpec AM M α Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec'.toNDEventSpec
    abstract := ev.abstract
    strengthening := ev.strengthening
    simulation := fun m x => by simp
                                intros Hinv Hgrd _ m' Heff am Href
                                apply ev.simulation m x Hinv Hgrd m' Heff am Href
  }

@[simp]
def newRNDEvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : RNDEventSpec' AM M α) : OrdinaryRNDEvent AM M α Unit :=
  newRNDEvent ev.toRNDEventSpec

structure RNDEventSpec'' (AM) [Machine ACTX AM]
                         (M) [Machine CTX M]
                         [Refinement AM M]
  extends NDEventSpec'' M where

  abstract : OrdinaryNDEvent AM Unit Unit

  strengthening (m : M):
    Machine.invariant m
    → guard m
    → ∀ am, refine am m
      → abstract.guard am ()

  simulation (m : M):
    Machine.invariant m
    → guard m
    → ∀ m', effect m m'
      → ∀ am, refine am m
        → ∃ am', abstract.effect am () ((), am')
                 ∧ refine am' m'

def RNDEventSpec''.toRNDEventSpec [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : RNDEventSpec'' AM M) : RNDEventSpec AM M Unit Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec''.toNDEventSpec
    abstract := ev.abstract
    strengthening := fun m () => by apply ev.strengthening
    simulation := fun m () => by simp
                                 intros Hinv Hgrd _ m' Heff am Href
                                 apply ev.simulation <;> assumption
  }

@[simp]
def newRNDEvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : RNDEventSpec'' AM M) : OrdinaryRNDEvent AM M Unit Unit :=
  newRNDEvent ev.toRNDEventSpec

/- Initialization events -/

structure _InitRNDEventPO  [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
   (ev : _NDEvent M α β) (kind : EventKind)
   extends _InitNDEventPO ev kind where

  abstract : _NDEvent AM α β

  strengthening (x : α):
    ev.guard Machine.reset x
    → ∀ am, refine (self:=instR) am Machine.reset
      → abstract.guard am x

  simulation (x : α):
    ev.guard Machine.reset x
    → ∀ y, ∀ m', ev.effect Machine.reset x (y, m')
      -- XXX : some constraint on output ?
      → ∀ am, refine (self:=instR) am Machine.reset
        → ∃ am', abstract.effect am x (y, am')
                 ∧ refine am' m'

structure InitRNDEvent (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M] (α) (β) extends _NDEvent M α β where
  po : _InitRNDEventPO (instR:=instR) to_NDEvent EventKind.InitNonDet

@[simp]
def InitRNDEvent.init  [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (ev : InitRNDEvent AM M α β) (x : α) (nxt : β × M) :=
  ev.effect Machine.reset x nxt

@[simp]
def InitRNDEvent.init'  [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (ev : InitRNDEvent AM M Unit β) (nxt: β × M) :=
  ev.init () nxt

@[simp]
def InitRNDEvent.init''  [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (ev : InitRNDEvent AM M Unit Unit) (m : M) :=
  ev.init' ((), m)

structure InitRNDEventSpec (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M] (α) (β)
  extends InitNDEventSpec M α β where

  abstract : InitNDEvent AM α β

  strengthening (x : α):
    guard x
    → abstract.guard Machine.reset x

  simulation (x : α):
    guard x
    → ∀ y, ∀ m', init x (y, m')
      -- XXX : some constraint on output ?
      → ∃ am', abstract.effect Machine.reset x (y, am')
               ∧ refine am' m'

@[simp]
def newInitRNDEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : InitRNDEventSpec AM M α β) : InitRNDEvent AM M α β :=
  {
    guard := fun m x => m = Machine.reset ∧ ev.guard x
    effect := fun _ x (y, m') => ev.init x (y, m')
    po := {
      safety := fun x => by simp
                            intros Hgrd y m' Hini
                            apply ev.safety (y:=y) x Hgrd
                            assumption
      feasibility := fun x => by simp
                                 intro Hgrd
                                 apply ev.feasibility x Hgrd
      abstract := ev.abstract.to_NDEvent
      strengthening := fun x => by simp
                                   intros Hgrd am Href
                                   have Hstr := ev.strengthening x Hgrd
                                   have Hax := refine_reset am Href
                                   rw [Hax]
                                   assumption
      simulation := fun x => by simp
                                intro Hgrd y m' Hini am Href
                                have Hsim := ev.simulation x Hgrd y m' Hini
                                have Hax := refine_reset am Href
                                rw [Hax]
                                assumption
    }
  }

structure InitRNDEventSpec' (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M] (α)
  extends InitNDEventSpec M α Unit where

  abstract : InitNDEvent AM α Unit

  strengthening (x : α):
    guard x
    → abstract.guard Machine.reset x

  simulation (x : α):
    guard x
    → ∀ m', init x ((), m')
      → ∃ am', abstract.effect Machine.reset x ((), am')
               ∧ refine am' m'

def InitRNDEventSpec_from_InitRNDEventSpec' [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (ev : InitRNDEventSpec' AM M α) : InitRNDEventSpec AM M α Unit :=
{
  guard := ev.guard
  init := ev.init
  safety := ev.safety
  feasibility := ev.feasibility
  abstract := ev.abstract
  strengthening := ev.strengthening
  simulation := fun x => by simp
                            intros Hgrd _ m' Hini
                            have Hsim := ev.simulation x Hgrd m' Hini
                            apply Hsim
}

@[simp]
def newInitRNDEvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : InitRNDEventSpec' AM M α) : InitRNDEvent AM M α Unit :=
  newInitRNDEvent (InitRNDEventSpec_from_InitRNDEventSpec' ev)

structure InitRNDEventSpec'' (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  extends InitNDEventSpec M Unit Unit where

  abstract : InitNDEvent AM Unit Unit

  strengthening:
    guard ()
    → abstract.guard Machine.reset ()

  simulation:
    guard ()
    → ∀ m', init () ((), m')
      → ∃ am', abstract.effect Machine.reset () ((), am')
               ∧ refine am' m'

def InitRNDEventSpec_from_InitRNDEventSpec'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M] (ev : InitRNDEventSpec'' AM M) : InitRNDEventSpec AM M Unit Unit :=
{
  guard := ev.guard
  init := ev.init
  safety := ev.safety
  feasibility := ev.feasibility
  abstract := ev.abstract
  strengthening := fun () => ev.strengthening
  simulation := fun () => by simp
                             intros Hgrd _ m' Hini
                             have Hsim := ev.simulation Hgrd m' Hini
                             apply Hsim
}

@[simp]
def newInitRNDEvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : InitRNDEventSpec'' AM M) : InitRNDEvent AM M Unit Unit :=
  newInitRNDEvent (InitRNDEventSpec_from_InitRNDEventSpec'' ev)
