
/-
  Reuse of abstract events
-/

import EventSystems.Refinement.Relational.Basic
import EventSystems.Refinement.Relational.Convergent

open Refinement

/-
 Q : is there a better way to ease the definition of abstract events ? -/

structure __AbstractREventSpec (AM) [Machine ACTX AM]
                               (M) [Machine CTX M]
                               [Refinement AM M] where

  lift (m: M) : AM

  lift_ref (m : M):
    Machine.invariant m → refine (lift m) m

  refine_uniq (am am' : AM) (m : M):
    Machine.invariant m
    → refine am m → refine am' m
    → am = am'


structure _AbstractREventSpec (AM) [Machine ACTX AM]
                              (M) [Machine CTX M]
                              [Refinement AM M] (α)

  extends __AbstractREventSpec AM M  where

  unlift (am am' : AM) (m : M) (x : α): M

structure AbstractREventSpec (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                            [Refinement AM M]
  {α β} (abstract : _Event AM α β)
          extends _AbstractREventSpec AM M α where

  step_ref (m : M) (x : α):
    Machine.invariant m
    → abstract.guard (lift m) x
    → let (_, am') := abstract.action (lift m) x
      refine am' (unlift (lift m) am' m x)

  step_safe (m : M) (x : α):
    Machine.invariant m
    → abstract.guard (lift m) x
    → let (_, am') := abstract.action (lift m) x
      Machine.invariant am' -- redundant but useful
      → Machine.invariant (unlift (lift m) am' m x)

@[simp]
def newAbstractREvent [Machine ACTX AM] [Machine CTX M] [instR:Refinement AM M]
  (abs : OrdinaryEvent AM α β) (ev : AbstractREventSpec AM M abs.to_Event) : OrdinaryREvent AM M α β :=
  { guard := fun (m : M) (x : α) => abs.guard (ev.lift m) x
    action := fun (m : M) (x : α) => let am := ev.lift m
                                     let (y, am') := abs.action am x
                                     (y, ev.unlift am am' m x)
    po := {
      safety := fun (m : M) (x : α) => by
        simp
        intros Hinv Hgrd
        have Href := ev.lift_ref m Hinv
        have Hainv := Refinement.refine_safe (ev.lift m) m Hinv Href
        have Hsafe := abs.po.safety (ev.lift m) x Hainv Hgrd
        apply ev.step_safe m x Hinv Hgrd Hsafe

      lift_in := id
      lift_out := id

      abstract := abs.to_Event

      strengthening := fun m x => by simp
                                     intros Hinv Hgrd am Href
                                     have Href' := ev.lift_ref m Hinv
                                     have Ham: am = ev.lift m := by
                                       apply ev.refine_uniq am (ev.lift m) m <;> assumption
                                     rw [Ham]
                                     assumption

      simulation := fun m x => by simp
                                  intros Hinv Hgrd am Href
                                  have Href' := ev.lift_ref m Hinv
                                  have Ham: am = ev.lift m := by
                                    apply ev.refine_uniq am (ev.lift m) m <;> assumption
                                  rw [Ham]
                                  constructor
                                  · simp
                                  apply ev.step_ref m x Hinv Hgrd
    }
  }

@[simp]
def newAbstractREvent' [Machine ACTX AM] [Machine CTX M] [instR:Refinement AM M]
  (abs : OrdinaryEvent AM α Unit) (ev : AbstractREventSpec AM M abs.to_Event) : OrdinaryREvent AM M α Unit :=
  newAbstractREvent abs ev

structure _AbstractREventSpec'' (AM) [Machine ACTX AM]
                                (M) [Machine CTX M]
                                [Refinement AM M]

  extends __AbstractREventSpec AM M  where

  unlift (am am' : AM) (m : M): M

structure AbstractREventSpec'' (AM) [Machine ACTX AM]
                               (M) [Machine CTX M]
                               [Refinement AM M]
  (abstract : _Event AM Unit Unit)
          extends _AbstractREventSpec'' AM M where

  step_ref (m : M):
    Machine.invariant m
    → abstract.guard (lift m) ()
    → let ((), am') := abstract.action (lift m) ()
      refine am' (unlift (lift m) am' m)

  step_safe (m : M):
    Machine.invariant m
    → abstract.guard (lift m) ()
    → let (_, am') := abstract.action (lift m) ()
      Machine.invariant am' -- redundant but useful
      → Machine.invariant (unlift (lift m) am' m)

@[simp]
def AbstractREventSpec''.toAbstractREventSpec [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
    (abs : _Event AM Unit Unit) (ev : AbstractREventSpec'' AM M abs) : AbstractREventSpec AM M abs :=
  {
    to__AbstractREventSpec := ev.to__AbstractREventSpec
    unlift := fun am am' m _ => ev.unlift am am' m
    step_ref := fun m () => ev.step_ref m
    step_safe := fun m () => ev.step_safe m
  }


@[simp]
def newAbstractREvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM Unit Unit) (ev : AbstractREventSpec'' AM M abs.to_Event) : OrdinaryREvent AM M Unit Unit :=
  newAbstractREvent abs ev.toAbstractREventSpec

structure AbstractInitREventSpec (AM) [Machine ACTX AM]
                                 (M) [Machine CTX M]
                                 [Refinement AM M]
  {α β} (abstract : _Event AM α β)
          extends _AbstractREventSpec AM M α where

  step_ref (x : α):
    abstract.guard Machine.reset x
    → let (_, am') := abstract.action Machine.reset x
      refine am' (unlift Machine.reset am' Machine.reset x)

  step_safe (x : α):
    abstract.guard Machine.reset x
    → let (_, am') := abstract.action Machine.reset x
      Machine.invariant am' -- redundant but useful
      → Machine.invariant (unlift Machine.reset am' Machine.reset x)

@[simp]
def newAbstractInitREvent [Machine ACTX AM] [Machine CTX M] [instR:Refinement AM M]
  (abs : InitEvent AM α β) (ev : AbstractInitREventSpec AM M abs.to_Event) : InitREvent AM M α β :=
  { guard := fun (m : M) (x : α) => m = Machine.reset ∧ abs.guard Machine.reset x
    action := fun (m : M) (x : α) => let (y, am') := abs.action Machine.reset x
                                     (y, ev.unlift Machine.reset am' m x)
    po := {
      safety := fun x => by
        simp
        intro Hgrd
        have Hasafe := abs.po.safety x Hgrd
        have Hss := ev.step_safe x Hgrd Hasafe
        assumption

      lift_in := id
      lift_out := id

      abstract := abs.to_Event

      strengthening := fun x => by
        simp
        intros Hgrd am Href
        have Hres := refine_reset am Href
        rw [Hres]
        assumption

      simulation := fun x => by
        simp
        intros Hgrd am Href
        have Hres := refine_reset am Href
        simp [Hres]
        apply ev.step_ref x Hgrd
    }
  }

@[simp]
def newAbstractInitREvent' [Machine ACTX AM] [Machine CTX M] [instR:Refinement AM M]
  (abs : InitEvent AM α Unit) (ev : AbstractInitREventSpec AM M abs.to_Event) : InitREvent AM M α Unit :=
  newAbstractInitREvent abs ev

structure AbstractInitREventSpec'' (AM) [Machine ACTX AM]
                                 (M) [Machine CTX M]
                                 [Refinement AM M]
  (abstract : _Event AM Unit Unit)
       extends _AbstractREventSpec'' AM M where

  step_ref:
    abstract.guard Machine.reset ()
    → let ((), am') := abstract.action Machine.reset ()
      refine am' (unlift Machine.reset am' Machine.reset)

  step_safe :
    abstract.guard Machine.reset ()
    → let ((), am') := abstract.action Machine.reset ()
      Machine.invariant am' -- redundant but useful
      → Machine.invariant (unlift Machine.reset am' Machine.reset)

@[simp]
def AbstractInitREventSpec''.toAbstractInitREventSpec [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
    (abs : _Event AM Unit Unit) (ev : AbstractInitREventSpec'' AM M abs) : AbstractInitREventSpec AM M abs :=
  {
    to__AbstractREventSpec := ev.to__AbstractREventSpec
    unlift := fun am am' m _ => ev.unlift am am' m
    step_ref := fun () => ev.step_ref
    step_safe := fun () => ev.step_safe
  }

@[simp]
def newAbstractRInitEvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : InitEvent AM Unit Unit) (ev : AbstractInitREventSpec'' AM M abs.to_Event) : InitREvent AM M Unit Unit :=
  newAbstractInitREvent abs ev.toAbstractInitREventSpec

structure AbstractAnticipatedREventSpec
              (v) [Preorder v]
              (AM) [Machine ACTX AM]
              (M) [Machine CTX M]
              [Refinement AM M]
  {α β} (abstract : AnticipatedEvent v AM α β)
          extends AbstractREventSpec AM M abstract.to_Event where

  step_variant (m : M) (x : α):
    Machine.invariant m
    → abstract.guard (lift m) x
    → let (_, am') := abstract.action (lift m) x
      Machine.invariant am' -- redundant but useful
      → abstract.po.variant (lift (unlift (lift m) am' m x))
      = abstract.po.variant am'

@[simp]
def newAbstractAnticipatedREvent [Preorder v]
                                 [Machine ACTX AM]
                                 [Machine CTX M]
                                 [instR:Refinement AM M]
  (abs : AnticipatedEvent v AM α β) (ev : AbstractAnticipatedREventSpec v AM M abs) : AnticipatedREvent v AM M α β :=
  let oev := newAbstractREvent abs.toOrdinaryEvent ev.toAbstractREventSpec
  {
    to_Event := oev.to_Event
    po := {
      safety := oev.po.safety
      lift_in := oev.po.lift_in
      lift_out := oev.po.lift_out
      abstract := abs.to_Event
      strengthening := oev.po.strengthening
      simulation := oev.po.simulation

      variant := fun m => abs.po.variant (ev.lift m)

      nonIncreasing := fun m x => by
        simp
        intros Hinv Hgrd
        have Hinv' := Refinement.refine_safe (ev.lift m) m Hinv (ev.lift_ref m Hinv)
        have Hainv := abs.po.safety (ev.lift m) x Hinv' Hgrd
        have Hni := abs.po.nonIncreasing (ev.lift m) x Hinv' Hgrd
        simp at Hni
        have Hsv := ev.step_variant m x Hinv Hgrd Hainv
        simp [oev]
        rw [Hsv]
        assumption
    }
  }

@[simp]
def newAbstractAnticipatedREvent' [Preorder v]
                                  [Machine ACTX AM]
                                  [Machine CTX M]
                                  [instR:Refinement AM M]
  (abs : AnticipatedEvent v AM α Unit) (ev : AbstractAnticipatedREventSpec v AM M abs) : AnticipatedREvent v AM M α Unit :=
  newAbstractAnticipatedREvent abs ev

structure AbstractAnticipatedREventSpec''
              (v) [Preorder v]
              (AM) [Machine ACTX AM]
              (M) [Machine CTX M]
              [Refinement AM M]
  (abstract : AnticipatedEvent v AM Unit Unit)
          extends AbstractREventSpec'' AM M abstract.to_Event where

  step_variant (m : M):
    Machine.invariant m
    → abstract.guard (lift m) ()
    → let ((), am') := abstract.action (lift m) ()
      Machine.invariant am' -- redundant but useful
      → abstract.po.variant (lift (unlift (lift m) am' m))
      = abstract.po.variant am'

@[simp]
def AbstractAnticipatedREventSpec''.toAbstractAnticipatedREventSpec [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : AnticipatedEvent v AM Unit Unit) (ev : AbstractAnticipatedREventSpec'' v AM M abs) : AbstractAnticipatedREventSpec v AM M abs :=
  {
    to__AbstractREventSpec := ev.to__AbstractREventSpec
    unlift := fun am am' m _ => ev.unlift am am' m
    step_ref := fun m _ => ev.step_ref m
    step_safe := fun m _ => ev.step_safe m
    step_variant := fun m _ => ev.step_variant m
  }

@[simp]
def newAbstractAnticipatedREvent'' [Preorder v]
                                  [Machine ACTX AM]
                                  [Machine CTX M]
                                  [Refinement AM M]
  (abs : AnticipatedEvent v AM Unit Unit) (ev : AbstractAnticipatedREventSpec'' v AM M abs) : AnticipatedREvent v AM M Unit Unit :=
  newAbstractAnticipatedREvent abs ev.toAbstractAnticipatedREventSpec

@[simp]
def newAbstractConvergentREvent  [Preorder v] [WellFoundedLT v]
                                 [Machine ACTX AM]
                                 [Machine CTX M]
                                 [instR:Refinement AM M]
  (abs : ConvergentEvent v AM α β) (ev : AbstractAnticipatedREventSpec v AM M abs.toAnticipatedEvent) : ConvergentREvent v AM M α β :=
  let oev := newAbstractAnticipatedREvent abs.toAnticipatedEvent ev
  {
    to_Event := oev.to_Event
    po := {
      safety := oev.po.safety
      lift_in := oev.po.lift_in
      lift_out := oev.po.lift_out
      abstract := abs.to_Event
      strengthening := oev.po.strengthening
      simulation := oev.po.simulation
      variant := oev.po.variant
      nonIncreasing := oev.po.nonIncreasing

      convergence := fun m x => by
        simp [oev]
        intros Hinv Hgrd
        have Hinv' := Refinement.refine_safe (ev.lift m) m Hinv (ev.lift_ref m Hinv)
        have Hainv := abs.po.safety (ev.lift m) x Hinv' Hgrd
        have Hcv := abs.po.convergence (ev.lift m) x Hinv' Hgrd
        simp at Hcv
        have Hsv := ev.step_variant m x Hinv Hgrd Hainv
        simp at Hsv
        rw [Hsv]
        assumption
    }
  }

@[simp]
def newAbstractConvergentREvent'  [Preorder v] [WellFoundedLT v]
                                  [Machine ACTX AM]
                                  [Machine CTX M]
                                  [instR:Refinement AM M]
  (abs : ConvergentEvent v AM α Unit) (ev : AbstractAnticipatedREventSpec v AM M abs.toAnticipatedEvent) : ConvergentREvent v AM M α Unit :=
  newAbstractConvergentREvent abs ev

@[simp]
def newAbstractConvergentREvent''  [Preorder v] [WellFoundedLT v]
                                   [Machine ACTX AM]
                                   [Machine CTX M]
                                   [Refinement AM M]
  (abs : ConvergentEvent v AM Unit Unit) (ev : AbstractAnticipatedREventSpec'' v AM M abs.toAnticipatedEvent) : ConvergentREvent v AM M Unit Unit :=
  newAbstractConvergentREvent abs ev.toAbstractAnticipatedREventSpec
