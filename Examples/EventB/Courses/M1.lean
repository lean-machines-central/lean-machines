
import Examples.EventB.Courses.M0

namespace CoursesSpec

structure MembersCtx where
  members : Finset Member

structure ParticipantsCtx extends MembersCtx where
  participants : Finset Member
  parts_prop : participants ⊆ members

structure InstructorsCtx extends M0.Context, MembersCtx where
  instructors : Finset Member
  instr_mem_prop : instructors ⊆ members
  instr_fun : Course → Member
  intr_fun_prop : ∀ c, c ∈ availableCourses → instr_fun c ∈ instructors

structure M1.Context extends ParticipantsCtx, InstructorsCtx

structure M1 (ctx : M1.Context) extends M0 ctx.toContext where
  inscriptions : Finset (Course × Member)

/-
theorem M1.ctx₁ (_ : M1 ctx):
  ctx.maxOpenedCourses > 0 :=
by
  cases ctx.toContext ; simp [*]

theorem M1.ctx₂ (_ : M1 ctx):
  ctx.maxOpenedCourses ≤ ctx.availableCourses.card :=
by
  cases ctx.toContext ; simp [*]

-/

def M1.invariant₁ (m : M1 ctx) : Prop :=
  m.inscriptions ⊆ m.openedCourses ×ˢ ctx.participants

theorem M1.invariants₁' (m : M1 ctx):
  m.invariant₁ →
  ∀ i ∈ m.inscriptions, i.1 ∈ m.openedCourses ∧ i.2 ∈ ctx.participants :=
by
  simp [invariant₁]
  intros Hinv₁ c p
  intro Hins
  have Hcp: (c, p) ∈ m.openedCourses ×ˢ ctx.participants := by
    exact Hinv₁ Hins
  apply Finset.mem_product (p:=(c, p)).1
  assumption

def M1.invariant₂ (m : M1 ctx) : Prop :=
  ∀ i ∈ m.inscriptions, ctx.instr_fun i.1 ≠ i.2

def M1.reset : M1 ctx :=
  let m0 := M0.reset ctx.toContext
  { m0 with inscriptions := ∅ }

instance: Machine M1.Context (M1 ctx) where
  context := ctx
  invariant m := M0.invariant₁ m.toM0 ∧ M0.invariant₂ m.toM0
                 ∧ M1.invariant₁ m ∧ M1.invariant₂ m
  reset := M1.reset

@[simp]
def M1.lift (m : M1 ctx) : M0 ctx.toContext :=
  ⟨m.openedCourses⟩

theorem M1.lift_safe (m : M1 ctx):
  Machine.invariant m → Machine.invariant (M1.lift m) :=
by
  simp [Machine.invariant]
  intros Hinv₁ Hinv₂ _ _
  constructor
  case left =>
    simp [M0.invariant₁]
    simp [M1.invariant₁, M0.invariant₁] at Hinv₁
    assumption
  case right =>
    simp [M0.invariant₂]
    simp [M1.invariant₂, M0.invariant₂] at Hinv₂
    assumption


@[simp]
def M1.unlift (m1 : M1 ctx) (m0' : M0 ctx.toContext) : M1 ctx:=
  { m0' with inscriptions := m1.inscriptions}

-- this is an interesting property : the abstract machine can move almost "freely"
theorem M1.unlift_safe (m1 : M1 ctx) (m0 : M0 ctx.toContext):
  m1.openedCourses = m0.openedCourses
  → Machine.invariant m1 → Machine.invariant m0
  → Machine.invariant (M1.unlift m1 m0) :=
by
  simp [Machine.invariant]
  intros Hcs _ _ Hinv₃ Hinv₄ Hainv₁ Hainv₂
  constructor
  · simp [M1.invariant₁, M0.invariant₁] at *
    assumption
  · constructor
    · simp [M1.invariant₂, M0.invariant₂] at *
      assumption
    · constructor
      · simp [M1.invariant₁] at *
        rw [Hcs] at Hinv₃
        assumption
      · simp [M1.invariant₂] at *
        assumption

/-

TODO

instance: SRefinement (M0 ctx.toContext) (M1 ctx) where
  refine := defaultRefine M1.lift
  refine_inv m am := by simp
                        intros Hinv Hlift
                        rw [Hlift]
                        apply M1.lift_safe
                        assumption
  refine_uniq m am am' := by simp
                             intros _ Ham Ham'
                             rw [Ham, ←Ham']
  lift := M1.lift
  lift_ref m := by simp

  unlift := M1.unlift
  lift_unlift m am' := by simp

namespace M1
namespace Init

@[local simp]
def init : M1 ctx :=
  let m0 : M0 ctx.toContext := M0.Init.init
  { m0 with inscriptions := ∅}

example: let m1 : M1 ctx := init
         m1.openedCourses = ∅ := by rfl

theorem PO_safety₁:
  @invariant₁ ctx init :=
by
  simp [M1.invariant₁]

theorem PO_safety₂:
  @invariant₂ ctx init :=
by
  simp [M1.invariant₂]

end Init

def Init : SRInitEvent (M0 ctx.toContext) (M1 ctx) Unit Unit := newSRInitEvent' {
  init := Init.init
  safety := by simp [Machine.invariant, M1.Init.PO_safety₁, M1.Init.PO_safety₂]
               constructor
               · apply M0.Init.PO_safety₁
               · apply M0.Init.PO_safety₂
  abstract := M0.Init
  strengthening := by simp [M0.Init, newInitEvent']
  simulation := by rfl
}

def OpenCourses : SRNDEvent (M0 ctx.toContext) (M1 ctx) Unit Unit :=
  newAbstractSRNDEvent' {
    event := M0.OpenCourses.toNDEvent
    step_inv := fun m1 m1' =>
      by simp [Machine.invariant, M0.OpenCourses, FRefinement.lift, SRefinement.unlift]
         intros _ _ Hinv₁ Hinv₂ _ cs _ _ Hact₃ _ Hainv'₁ Hainv'₂
         constructor
         · assumption
         · constructor
           · assumption
           · constructor
             · simp [invariant₁] at *
               rw [Hact₃]
               have Hcup: m1.openedCourses ×ˢ ctx.participants ⊆ (m1.openedCourses ∪ cs) ×ˢ ctx.participants := by
                 apply Finset.product_subset_product_left
                 · apply Finset.subset_union_left
               exact Finset.Subset.trans Hinv₁ Hcup
             · simp [invariant₂] at *
               assumption
    event_ok := by simp [M0.OpenCourses]
  }

namespace CloseCourses

@[local simp]
def guard (m : M1 ctx) (cs : Finset Course) :=
  M0.CloseCourses.guard m.toM0 cs

def removeCourses (cs : Finset Course) (is : Finset (Course × Member)) : Finset (Course × Member) :=
  Finset.filter (fun (c', _) => c' ∉ cs) is

theorem removeCourses_mem (cs : Finset Course) (is : Finset (Course × Member)):
  ∀ cp, cp ∈ removeCourses cs is → cp ∈ is :=
by
  simp [removeCourses]
  intros _ _ H₁ _
  assumption

theorem removeCourses_memCourse (cs : Finset Course) (is : Finset (Course × Member)):
  ∀ cp, cp ∈ removeCourses cs is → cp.1 ∉ cs :=
by
  simp [removeCourses]

theorem removeCourses_notmem (cs : Finset Course) (is : Finset (Course × Member)):
  ∀ cp ∈ is, cp.1 ∉ cs → cp ∈ removeCourses cs is :=
by
  simp [removeCourses]
  intros c p Hcp Hc
  simp [Hcp, Hc]

@[local simp]
def action (m : M1 ctx) (cs : Finset Course) : M1 ctx :=
  let am' : M0 ctx.toContext := M0.CloseCourses.action m.toM0 cs
  { am' with inscriptions := removeCourses cs m.inscriptions}

theorem PO_safety₁ (m : M1 ctx) (cs : Finset Course):
  invariant₁ m
  → invariant₁ (action m cs) :=
by
  simp [invariant₁, M0.CloseCourses.guard]
  intros Hinv₁ cp Hrem
  simp [removeCourses] at Hrem
  have Hcp := Hinv₁ Hrem.1
  apply Finset.mem_product.2
  constructor
  · refine Finset.mem_sdiff.mpr ?left.a
    constructor
    · apply (Finset.mem_product.1 Hcp).left
    · exact Hrem.2
  · apply (Finset.mem_product.1 Hcp).right

theorem PO_safety₂ (cs : Finset Course) (m : M1 ctx):
  invariant₂ m
  → invariant₂ (action m cs) :=
by
  simp [invariant₂, removeCourses]
  intros Hinv₂ c p Hrem _
  apply Hinv₂
  assumption


@[local simp]
def variant (m : M1 ctx) := M0.CloseCourses.variant m.toM0

theorem PO_convergence (m : M1 ctx) (cs : Finset Course):
  Machine.invariant m
  → guard m cs
  → variant (action m cs) < variant m :=
by
  simp [Machine.invariant, -guard]
  intros _ _ _ _ Hgrd
  apply M0.CloseCourses.PO_convergence
  assumption

theorem PO_strengthening (m1 : M1 ctx) (cs : Finset Course):
  Machine.invariant m1
    → guard m1 cs
    → let m0 : M0 ctx.toContext := FRefinement.lift m1
      M0.CloseCourses.toEvent.guard m0 cs :=
by
  simp [FRefinement.lift, M0.CloseCourses, newConvergentEvent]

theorem PO_simulation (m1 : M1 ctx) (cs : Finset Course):
  Machine.invariant m1
    → guard m1 cs
    → let m0 : M0 ctx.toContext := FRefinement.lift m1
      M0.CloseCourses.toEvent.action m0 cs = FRefinement.lift (action m1 cs) :=
by
  simp [FRefinement.lift, M0.CloseCourses, newConvergentEvent]

end CloseCourses

def CloseCourses : SRConvergentEvent Nat (M0 ctx.toContext) (M1 ctx) (Finset Course) (Finset Course):= newSRConvergentEvent {
  guard := CloseCourses.guard
  action := CloseCourses.action
  safety := fun m cs => by intros Hinv _
                           simp [Machine.invariant] at *
                           simp [Hinv, CloseCourses.PO_safety₁,
                                      CloseCourses.PO_safety₂]
                           constructor
                           · apply M0.CloseCourses.PO_safety₁ ; simp [Hinv]
                           · apply M0.CloseCourses.PO_safety₂ ; simp [Hinv]
  absParam := id
  abstract := M0.CloseCourses.toEvent
  variant := CloseCourses.variant
  convergence := CloseCourses.PO_convergence
  strengthening := CloseCourses.PO_strengthening
  simulation := CloseCourses.PO_simulation
}

namespace Register

@[local simp]
def unregistered? (is : Finset (Course × Member)) (c : Course) (p : Member)  :=
  (c, p) ∉ is

@[local simp]
def guard (m : M1 ctx) (p : Member) (c : Course) :=
  c ∈ m.openedCourses ∧ p ∈ ctx.participants ∧ ctx.instr_fun c ≠ p
  ∧  unregistered? m.inscriptions c p

@[local simp]
def action (m : M1 ctx) (p : Member) (c : Course) : M1 ctx :=
  { openedCourses := m.openedCourses,
    inscriptions := insert (c,p) m.inscriptions }

theorem PO_safety₁ (m : M1 ctx) (p : Member) (c : Course) :
  Machine.invariant m → guard m p c
  → invariant₁ (action m p c) :=
by
  simp [Machine.invariant, M0.invariant₁, M0.invariant₂, invariant₁, invariant₂]
  intros Hainv₁ _ Hinv₁ _ Hgrd₁ Hgrd₂ _ _
  apply Finset.insert_subset
  · have Hc: c ∈ ctx.availableCourses := by exact Hainv₁ Hgrd₁
    have Hp: p ∈ ctx.participants := by exact Hgrd₂
    simp [Hc, Hp, Hgrd₁]
  · assumption

theorem PO_safety₂ (m : M1 ctx) (p : Member) (c : Course) :
  invariant₂ m → guard m p c
  → invariant₂ (action m p c) :=
by
  simp [Machine.invariant, invariant₂]
  intros Hinv₂ _ _ Hfun _
  simp [*]
  exact fun a b a_1 => Hinv₂ a b a_1

def variant (m : M1 ctx) :=
  (Finset.card m.openedCourses * Finset.card ctx.participants) - Finset.card m.inscriptions

theorem PO_convergence (m : M1 ctx) (p : Member) (c : Course) :
  Machine.invariant m
  → guard m p c
  → variant (action m p c) < variant m :=
by
  simp [Machine.invariant, variant]
  intros Hainv₁ _ Hinv₁ _ Hgrd₁ Hgrd₂ _ Hgrd₄
  have Hins: (insert (c, p) m.inscriptions).card = m.inscriptions.card + 1 := by
    exact Finset.card_insert_of_not_mem Hgrd₄
  simp [Hins] ; clear Hins
  simp [invariant₁] at Hinv₁
  simp [M0.invariant₁] at Hainv₁

  have Hsub: m.inscriptions ⊂ m.openedCourses ×ˢ ctx.participants := by
    apply (Finset.ssubset_iff_of_subset Hinv₁).2
    exists (c, p)
    constructor
    · exact Finset.mk_mem_product Hgrd₁ Hgrd₂
    · assumption

  have Hins: m.inscriptions.card < (m.openedCourses ×ˢ ctx.participants).card := by
    exact Finset.card_lt_card Hsub

  rw [Finset.card_product] at Hins

  apply Nat.sub_lt_sub_left
  · assumption
  · simp_arith

theorem PO_simulation (m1 : M1 ctx) (p : Member) (c : Course):
    Machine.invariant m1
    → guard m1 p c
    → let m0 : M0 ctx.toContext := M1.lift m1
      FRefinement.lift (action m1 p c) = m0 :=
by
  simp [FRefinement.lift]

end Register

def Register : SRConvergentEvent Nat (M0 ctx.toContext) (M1 ctx) (Member × Course) (Member × Course) :=
  newConcreteSREvent {
    guard := fun m (p,c) => Register.guard m p c
    action := fun m (p,c) => Register.action m p c
    safety := fun m (p,c) => by simp [Machine.invariant]
                                intros Hainv₁ Hainv₂ Hinv₁ Hinv₂ Hgrd
                                constructor
                                · simp [Register.action, M0.invariant₁] at *
                                  exact Hainv₁
                                · constructor
                                  · simp [Register.action, M0.invariant₂] at *
                                    exact Hainv₂
                                  · constructor
                                    · apply Register.PO_safety₁
                                      · simp [Machine.invariant, *]
                                      · assumption
                                    · exact Register.PO_safety₂ m p c Hinv₂ Hgrd


    variant := Register.variant
    convergence := fun m (p,c) => Register.PO_convergence m p c
    simulation := fun m (p,c) => Register.PO_simulation m p c
  }

end M1

-/

end CoursesSpec
