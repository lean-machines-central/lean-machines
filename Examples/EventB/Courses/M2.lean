
import Examples.EventB.Courses.M1

namespace CoursesSpec

structure M2.Context extends M1.Context

structure M2 (ctx : M2.Context) where
  attendants : Course → Finset Member
  domain : Finset Course

def M2.invariant₁ (m2 : M2 ctx) :=
  m2.domain ⊆ ctx.availableCourses

def M2.invariant₂ (m2 : M2 ctx) :=
  m2.domain.card ≤  ctx.maxOpenedCourses

def M2.invariant₃ (m2 : M2 ctx) :=
  ∀ c, m2.attendants c ≠ ∅ → c ∈ m2.domain

def M2.invariant₄ (m2 : M2 ctx) :=
  ∀ c, m2.attendants c ⊆ ctx.participants

def M2.invariant₅ (m2 : M2 ctx) :=
  ∀ c, ∀ m, m ∈ m2.attendants c → ctx.instr_fun c ≠ m

@[simp]
def M2.reset : M2 ctx :=
  { domain := ∅,
    attendants := fun _ => ∅ }

instance: Machine M2.Context (M2 ctx) where
  context := ctx
  invariant m := M2.invariant₁ m ∧ M2.invariant₂ m ∧ M2.invariant₃ m ∧ M2.invariant₄ m ∧ M2.invariant₅ m
  reset := M2.reset

def M2.refine₁ (m1 : M1 ctx.toContext_1) (m2 : M2 ctx) :=
  m2.domain = m1.toM0.openedCourses

def M2.refine₂ (m1 : M1 ctx.toContext_1) (m2 : M2 ctx) :=
  ∀ c ∈ m2.domain, ∀ p : Member, p ∈ m2.attendants c → (c, p) ∈ m1.inscriptions

def M2.refine₃ (m1 : M1 ctx.toContext_1) (m2 : M2 ctx) :=
  ∀ c : Course, ∀ p : Member, (c, p) ∈ m1.inscriptions → c ∈ m2.domain ∧ p ∈ m2.attendants c

theorem M2.refine_inv (m1 : M1 ctx.toContext_1) (m2 : M2 ctx):
    Machine.invariant m2
    → M2.refine₁ m1 m2
    → M2.refine₂ m1 m2
    → M2.refine₃ m1 m2
    → Machine.invariant m1 :=
by
  simp [Machine.invariant]
  intros Hinv₁ Hinv₂ _ Hinv₄ Hinv₅ Href₁ Href₂ Href₃
  simp [refine₁] at Href₁
  simp [refine₂] at Href₂
  simp [refine₃] at Href₃
  constructor
  · simp [M0.invariant₁]
    simp [invariant₁] at Hinv₁
    simp [←Href₁, Hinv₁]
  constructor
  · simp [M0.invariant₂]
    simp [invariant₂] at Hinv₂
    simp [←Href₁, Hinv₂]
  constructor
  · simp [M1.invariant₁]
    intro (c, p) Hcp₁
    obtain ⟨Hcp₂, Hcp₃⟩ := Href₃ c p Hcp₁
    apply (Finset.mem_product (s:=m1.openedCourses) (t:=ctx.participants) (p:=(c, p))).2
    constructor
    · simp [←Href₁, Hcp₂]
    simp [invariant₄] at Hinv₄
    exact Hinv₄ c Hcp₃
  simp [M1.invariant₂]
  intros c p Hcp₁
  obtain ⟨_, Hcp₃⟩ := Href₃ c p Hcp₁
  simp [invariant₅] at Hinv₅
  intro Hfalse
  have Hinv₅' := Hinv₅ c
  rw [Hfalse] at Hinv₅'
  contradiction

instance: Refinement (M1 ctx.toContext_1) (M2 ctx) where
  refine := fun m1 m2 => M2.refine₁ m1 m2 ∧ M2.refine₂ m1 m2 ∧ M2.refine₃ m1 m2
  refine_safe := fun m1 m2 => by intros Hinv Href
                                 apply M2.refine_inv m1 m2 <;> simp [Hinv, Href]

namespace M2

namespace Init

@[local simp]
def init : M2 ctx :=
  { domain := ∅,
    attendants := fun _ => ∅ }

end Init

def Init : InitREvent (M1 ctx.toContext_1) (M2 ctx) Unit Unit :=
newInitREvent'' M1.Init.toInitEvent {
  init :=   { domain := ∅, attendants := fun _ => ∅ }
  safety := by simp [Machine.invariant, invariant₁, invariant₂, invariant₃, invariant₄, invariant₅,
                     Init.init, invariant₄, invariant₅]
  strengthening := by simp [M1.Init]
  simulation := by simp [Refinement.refine, Init.init, refine₁, refine₂, refine₃]
                   simp [M1.Init, M1.Init.init]
}

namespace OpenCourses

@[local simp]
def guard (m2 : M2 ctx) (cs : Finset Course) :=
  cs ≠ ∅ ∧ cs ⊆ ctx.availableCourses ∧ Disjoint cs m2.domain
  ∧ m2.domain.card + cs.card ≤ ctx.maxOpenedCourses

@[local simp]
def action (m2 : M2 ctx) (cs : Finset Course) : M2 ctx :=
  {domain := m2.domain ∪ cs
   attendants := m2.attendants }

theorem PO_safety₁ (m2 : M2 ctx) (cs : Finset Course):
  invariant₁ m2 → guard m2 cs
  → invariant₁ (action m2 cs) :=
by
  simp [invariant₁]
  intros Hinv₁ _ Hinv₃ _ _
  apply Finset.union_subset <;> assumption

theorem PO_safety₂ (m2 : M2 ctx) (cs : Finset Course):
  invariant₂ m2 → guard m2 cs
  → invariant₂ (action m2 cs) :=
by
  simp [invariant₂]
  intros _ _ _ _ Hinv₄
  have H₁ := Finset.card_union_le m2.domain cs
  exact Nat.le_trans H₁ Hinv₄

theorem PO_safety₃ (m2 : M2 ctx) (cs : Finset Course):
  invariant₃ m2 → guard m2 cs
  → invariant₃ (action m2 cs) :=
by
  simp [invariant₃]
  intros Hinv₁ _ _ _ _ c Hatt
  constructor
  apply Hinv₁ ; assumption

theorem PO_safety₄ (m2 : M2 ctx) (cs : Finset Course):
  invariant₄ m2 → guard m2 cs
  → invariant₄ (action m2 cs) :=
by
  simp [invariant₄]
  intros Hinv₄ _ _ _ _ c cs Hatt
  apply Hinv₄ c ; assumption

theorem PO_safety₅ (m2 : M2 ctx) (cs : Finset Course):
  invariant₅ m2 → guard m2 cs
  → invariant₅ (action m2 cs) :=
by
  simp [invariant₅]
  intros Hinv₅ _ _ _ _ c
  exact Hinv₅ c

@[local simp]
def variant (m2 : M2 ctx) := ctx.maxOpenedCourses - m2.domain.card

theorem PO_convergence (m2 : M2 ctx) (cs : Finset Course):
  guard m2 cs → variant (action m2 cs) < variant m2 :=
by
  simp
  intro Hgrd₁ _ Hgrd₃ Hgrd₄
  have H₁ := Finset.card_union_of_disjoint Hgrd₃
  rw [Finset.union_comm, H₁]
  clear H₁
  have H₂ : cs.card ≠ 0 := by
    simp [Hgrd₁]
  apply Nat.sub_lt_sub_left
  · apply Nat.lt_of_le_of_ne
    · exact le_of_add_le_left Hgrd₄
    · intro Hcontra
      rw [Hcontra] at Hgrd₄
      simp_arith [*] at Hgrd₄
  · apply Nat.lt_add_of_pos_left
    exact Nat.pos_of_ne_zero H₂

theorem PO_strengthening (m2 : M2 ctx) (cs : Finset Course):
  Machine.invariant m2 →
  guard m2 cs →
  ∀ (m1 : M1 ctx.toContext_1), Refinement.refine m1 m2
  → M1.OpenCourses.to_NDEvent.guard m1 () :=
by
  intros _ Hgrd am Href
  simp [M1.OpenCourses, M0.OpenCourses, FRefinement.lift, SRefinement.unlift]
  simp [OpenCourses.guard] at Hgrd
  simp [Refinement.refine, refine₁] at Href
  rw [←Href.left]
  intro Hfalse
  have H₁: cs.card ≤ 0 := by linarith
  simp at H₁
  have H₂ : cs ≠ ∅ := by simp [Hgrd]
  contradiction

theorem PO_simulation (m2 : M2 ctx) (cs : Finset Course):
  Machine.invariant m2 →
  guard m2 cs →
  ∀ (m1 : M1 ctx.toContext_1),
    Refinement.refine m1 m2 →
      ∃ (m1' : M1 ctx.toContext_1),
        M1.OpenCourses.to_NDEvent.effect m1 () ((), m1')
        ∧ Refinement.refine m1' (OpenCourses.action m2 cs) :=
by
  intros Hinv Hgrd m1 Href
  simp [M1.OpenCourses, M0.OpenCourses, FRefinement.lift, SRefinement.unlift]
  simp [Machine.invariant] at Hinv
  simp at Hgrd
  obtain ⟨Hgrd₁, Hgrd₂, Hgrd₃, Hgrd₄⟩ := Hgrd
  obtain ⟨Hinv₁ ,Hinv₂, Hinv₃, Hinv₄, Hinv₅⟩ := Hinv
  simp [invariant₁] at Hinv₁
  simp [invariant₂] at Hinv₂
  simp [invariant₃] at Hinv₃
  simp [invariant₄] at Hinv₄
  simp [invariant₅] at Hinv₅
  simp [Refinement.refine, refine₁, refine₂, refine₃] at Href
  obtain ⟨Href₁, Href₂, Href₃⟩ := Href
  exists ⟨⟨m1.openedCourses ∪ cs⟩, m1.inscriptions⟩
  simp
  constructor
  case left =>
    exists cs
    simp [*]
    rw [←Href₁]
    have Hcard := Finset.card_union_le m2.domain cs
    apply le_trans (b:=m2.domain.card + cs.card) Hcard Hgrd₄
  case right =>
    simp [Refinement.refine, refine₁, refine₂, refine₃, *]
    constructor
    · intros c Hc p Hp
      rw [←Href₁] at Hc
      cases Hc
      case _ Hc =>
        exact Href₂ c Hc p Hp
      case _ Hc =>
        have Hinv₃' := Hinv₃ c
        have Hcontra : c ∈ m2.domain := by
          apply Hinv₃'
          intro Hcontra
          rw [Hcontra] at Hp
          contradiction
        have Hcontra': c ∉ m2.domain := by
          apply Finset.disjoint_left (s:=cs) (t:=m2.domain).mp Hgrd₃ Hc
        contradiction
    -- next cases
    intros c p Hcp
    have Href₃' := Href₃ c p Hcp
    constructor
    · rw [←Href₁]
      simp [Href₃']
    -- final case
    simp [Href₃']

end OpenCourses

def OpenCourses : ConvergentRDetEvent Nat (M1 ctx.toContext_1) (M2 ctx) (Finset Course) Unit Unit Unit :=
  newConvergentRDetEvent' M1.OpenCourses.toOrdinaryNDEvent {
    guard := OpenCourses.guard
    action := OpenCourses.action
    lift_in := fun _ => ()
    safety := fun m2 cs => by simp [Machine.invariant]
                              intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hgrd
                              constructor
                              · apply OpenCourses.PO_safety₁ <;> assumption
                              constructor
                              · apply OpenCourses.PO_safety₂ <;> assumption
                              constructor
                              · apply OpenCourses.PO_safety₃ m2 cs <;> assumption
                              constructor
                              · apply OpenCourses.PO_safety₄ m2 cs <;> assumption
                              apply OpenCourses.PO_safety₅ m2 cs <;> assumption


    variant := OpenCourses.variant
    convergence := fun m2 cs => by
      simp [Machine.invariant]
      intros _ _ _ _ _ Hgrd
      apply OpenCourses.PO_convergence ; assumption


    strengthening := fun m cs => by simp ; apply OpenCourses.PO_strengthening

    simulation := fun m2 cs => by
      simp --; apply OpenCourses.PO_simulation m2 cs
      intros Hinv Hgrd am Href
      apply OpenCourses.PO_simulation m2 cs Hinv Hgrd am Href
  }

/-

TODO

namespace CloseCourses

@[local simp]
def guard (m2 : M2 ctx) (cs : Finset Course) :=
  cs ≠ ∅ ∧ cs ⊆ m2.domain

@[local simp]
def removeCourses (cs : Finset Course) (attnds : Course → Finset Member): Course → Finset Member :=
  fun (c : Course) => if c ∈ cs then ∅ else attnds c

@[local simp]
def action (m2 : M2 ctx) (cs : Finset Course) : M2 ctx :=
  {domain := m2.domain \ cs
   attendants := removeCourses cs m2.attendants }

theorem PO_safety₁ (m2 : M2 ctx) (cs : Finset Course):
  invariant₁ m2 → guard m2 cs
  → invariant₁ (action m2 cs) :=
by
  simp [invariant₁]
  intros Hinv₁ _ _
  have H₁ : m2.domain \ cs ⊆ m2.domain := by apply Finset.sdiff_subset
  exact Finset.Subset.trans H₁ Hinv₁

theorem PO_safety₂ (m2 : M2 ctx) (cs : Finset Course):
  invariant₂ m2 → guard m2 cs
  → invariant₂ (action m2 cs) :=
by
  simp [invariant₂]
  intros Hinv₁ _ _
  have H₁: m2.domain \ cs ⊆ m2.domain := by apply Finset.sdiff_subset
  have H₂: (m2.domain \ cs).card ≤ m2.domain.card := by exact Finset.card_le_card H₁
  exact Nat.le_trans H₂ Hinv₁

theorem PO_safety₃ (m2 : M2 ctx) (cs : Finset Course):
  invariant₃ m2 → guard m2 cs
  → invariant₃ (action m2 cs) :=
by
  simp [invariant₃]
  intros Hinv₃ _ _ c Hc Hatt
  constructor
  · apply Hinv₃ ; assumption
  · assumption

theorem PO_safety₄ (m2 : M2 ctx) (cs : Finset Course):
  invariant₄ m2 → guard m2 cs
  → invariant₄ (action m2 cs) :=
by
  simp [invariant₄]
  intros Hinv₄ _
  intros _ c
  split
  · exact Finset.empty_subset ctx.participants
  exact Hinv₄ c

theorem PO_safety₅ (m2 : M2 ctx) (cs : Finset Course):
  invariant₅ m2 → guard m2 cs
  → invariant₅ (action m2 cs) :=
by
  simp [invariant₅]
  intros Hinv₅ _ _ c
  split
  · simp
  · exact Hinv₅ c


@[local simp]
def variant (m2 : M2 ctx) := m2.domain.card

theorem Nat_sub_eq (a b : Nat):
  a - b = a → a = 0 ∨ b = 0 :=
by
  intro Hab
  cases a
  case zero =>
    apply Or.intro_left ; simp
  case succ a =>
    apply Or.intro_right
    --by_cases b = 0
    --case pos Hb => assumption
    --case neg Hb =>
    by_cases b ≤ Nat.succ a
    case pos Hb =>
       -- (Nat.succ a) - b = (Nat.succ a)  ==> Nat.succ a = Nat.succ a + b
       have H₁ : Nat.succ a = Nat.succ a + b := by exact Nat.eq_add_of_sub_eq Hb Hab
       exact Nat.add_left_cancel (id H₁.symm)
    case neg Hb' =>
      have H₁ : b < Nat.succ a := by
        apply Nat.lt_of_sub_ne_zero
        rw [Hab]
        simp_arith
      have Hcontra: b ≤ Nat.succ a := by exact Nat.le_of_lt H₁
      contradiction

theorem PO_convergence (m2 : M2 ctx) (cs : Finset Course):
  guard m2 cs → variant (action m2 cs) < variant m2 :=
by
  simp
  intros Hgrd₁ Hgrd₂
  have H₁: m2.domain \ cs ⊆ m2.domain := by apply Finset.sdiff_subset
  have H₂: (m2.domain \ cs).card ≤ m2.domain.card := by exact Finset.card_le_card H₁
  apply Nat.lt_of_le_of_ne
  · assumption
  · intros Hcontra
    have H₃ := Finset.card_sdiff Hgrd₂
    rw [H₃] at Hcontra
    have H₄ : m2.domain.card = 0 ∨ cs.card = 0 := by apply Nat_sub_eq ; assumption
    cases H₄
    case h₂.inl H₄ =>
      have H₅ : m2.domain = ∅ := by exact Finset.card_eq_zero.mp H₄
      rw [H₅] at Hgrd₂
      have H₅ : cs = ∅ := by exact Finset.subset_empty.mp Hgrd₂
      contradiction
    case h₂.inr H₄ =>
      have H₅ : cs = ∅ := by exact Finset.card_eq_zero.mp H₄
      contradiction

theorem PO_strengthening (m2: M2 ctx) (cs: Finset Course):
  Machine.invariant m2 →
  CloseCourses.guard m2 cs →
    ∀ (m1 : M1 ctx.toContext_1),
      Refinement.refine m2 m1
      → M1.CloseCourses.guard m1 cs :=
by
  intros _ Hgrd m1 Href
  simp at Hgrd
  obtain ⟨Hgrd₁, Hgrd₂⟩ := Hgrd
  simp [Refinement.refine] at Href
  obtain ⟨Href₁ , _, _⟩ := Href
  simp [M1.CloseCourses.guard]
  simp [refine₁] at Href₁
  simp [Hgrd₁, ←Href₁, Hgrd₂]

theorem PO_simulation (m2: M2 ctx) (cs: Finset Course):
  Machine.invariant m2 →
  CloseCourses.guard m2 cs →
    ∀ (m1 : M1 ctx.toContext_1),
      Refinement.refine m2 m1 →
        Refinement.refine (CloseCourses.action m2 cs)
          (M1.CloseCourses.action m1 cs) :=
by
  intros _ _ m1 Href
  obtain ⟨Href₁, Href₂, Href₃⟩ := Href
  simp [Refinement.refine] at *
  constructor
  · simp [refine₁] at *
    simp [M1.CloseCourses.action, Href₁]
  constructor
  · simp [refine₂] at *
    intros c Hc₁ Hc₂ p Hp
    simp [M1.CloseCourses.action]
    simp [Hc₂] at Hp
    have Href₂' := Href₂ c Hc₁ p Hp
    apply M1.CloseCourses.removeCourses_notmem <;> assumption
  simp [refine₃] at *
  simp [M1.CloseCourses.action]
  intros c p Hcp
  have Hc := M1.CloseCourses.removeCourses_memCourse cs m1.inscriptions (c,p) Hcp
  simp at Hc
  have Hcp' := M1.CloseCourses.removeCourses_mem cs m1.inscriptions (c,p) Hcp
  have ⟨Href₃',Href₃''⟩ := Href₃ c p Hcp'
  simp [Hc, Href₃', Href₃'']

end CloseCourses

def CloseCourses : RConvergentEvent Nat (M1 ctx.toContext_1) (M2 ctx) (Finset Course) (Finset Course) :=
  newRConvergentEvent {
    guard := CloseCourses.guard
    action := CloseCourses.action
    safety := fun m cs => by simp [Machine.invariant]
                             intros
                             constructor
                             · apply CloseCourses.PO_safety₁ <;> assumption
                             constructor
                             · apply CloseCourses.PO_safety₂ <;> assumption
                             constructor
                             · apply CloseCourses.PO_safety₃ <;> assumption
                             constructor
                             · apply CloseCourses.PO_safety₄ <;> assumption
                             apply CloseCourses.PO_safety₅ <;> assumption
    variant := CloseCourses.variant
    convergence := fun m cs => by intros ; apply CloseCourses.PO_convergence ; assumption
    absParam := id
    abstract := M1.CloseCourses.toEvent
    strengthening := fun m2 cs => by simp ; apply CloseCourses.PO_strengthening m2 cs
    simulation := fun m2 cs => by simp ; apply CloseCourses.PO_simulation m2 cs
  }

namespace Register

@[local simp]
def guard (m : M2 ctx) (p : Member) (c : Course) :=
  c ∈ m.domain ∧ p ∉ m.attendants c ∧ p ∈ ctx.participants ∧ ctx.instr_fun c ≠ p

@[local simp]
def action (m : M2 ctx) (p : Member) (c : Course) : M2 ctx :=
  { domain := m.domain,
    attendants := fun c' => if c' = c then (m.attendants c') ∪ {p}
                            else m.attendants c'
  }

theorem PO_safety₁ (m : M2 ctx) (p : Member) (c : Course) :
  invariant₁ m
  → invariant₁ (action m p c) :=
by
  simp [invariant₁]

theorem PO_safety₂ (m : M2 ctx) (p : Member) (c : Course) :
  invariant₂ m
  → invariant₂ (action m p c) :=
by
  simp [invariant₂]

theorem PO_safety₃ (m : M2 ctx) (p : Member) (c : Course) :
  invariant₃ m → c ∈ m.domain
  → invariant₃ (action m p c) :=
by
  simp [invariant₃]
  intros Hinv₃ Hgrd₁ c'
  split
  case inl Heq =>
    simp [Heq, Hgrd₁]
  case inr Hneq =>
    intro H₁
    apply Hinv₃ ; assumption

theorem PO_safety₄ (m : M2 ctx) (p : Member) (c : Course) :
  invariant₄ m → p ∈ ctx.participants
  → invariant₄ (action m p c) :=
by
  simp [invariant₄]
  intros Hinv₄ Hgrd₃ c'
  split
  case inl Heq =>
    rw [Heq]
    intro q Hq
    simp at Hq
    cases Hq
    case inl Hq =>
      have Hinv₄' := Hinv₄ c
      apply Hinv₄' ; assumption
    case inr Hq =>
      simp [Hq, Hgrd₃]
  case inr Heq =>
    apply Hinv₄

theorem PO_safety₅ (m2 : M2 ctx) (p : Member) (c : Course) :
  invariant₅ m2 → ctx.instr_fun c ≠ p
  → invariant₅ (action m2 p c) :=
by
  simp [invariant₅]
  intros Hinv₅ Hgrd₄ c'
  split
  case inl Heq =>
    simp [Heq]
    intro Hcut
    cases Hcut
    case inl Hc =>
      apply Hinv₅ c ; assumption
    case inr Hc =>
      contradiction

  case inr Hneq =>
    apply Hinv₅

def course_pairs (c : Course) (ps : Finset Member) : Finset (Course × Member):=
  ps.fold Union.union ∅ (fun p => {(c, p)})

theorem course_pairs_insert (c : Course) (ps : Finset Member):
  course_pairs c (insert p ps) = insert (c, p) (course_pairs c ps) :=
by
  simp [course_pairs]
  rfl

theorem course_pairs_insert_mem (c : Course) (ps : Finset Member):
  ∀ p ∈ ps, course_pairs c (insert p ps) = course_pairs c ps :=
by
  intros p Hp
  simp [course_pairs, Hp]

theorem course_pairs_notmem (c d : Course) (ps : Finset Member):
  c ≠ d → ∀ p, (d,p) ∉ course_pairs c ps :=
by
  intros Hneq p
  induction ps using Finset.induction
  case empty => simp [course_pairs]
  case insert e cs _ Hind =>
    rw [@course_pairs_insert]
    rw [@Finset.insert_eq]
    intro Hfalse
    simp at Hfalse
    cases Hfalse
    case inl Hfalse =>
      simp [Hfalse] at Hneq
    case inr Hfalse =>
      contradiction

theorem course_pairs_notmem' (c : Course) (ps : Finset Member):
  ∀ p ∉ ps, (c,p) ∉ course_pairs c ps :=
by
  intros p Hp
  induction ps using Finset.induction
  case empty => simp [course_pairs]
  case insert e ps _ Hind =>
    rw [@course_pairs_insert]
    rw [@Finset.insert_eq]
    simp
    simp at Hp
    intro Hfalse
    cases Hfalse
    case inl Hfalse =>
      simp [Hfalse] at Hp
    case inr Hfalse =>
      have Hind' : (c, p) ∉ course_pairs c ps := by
        apply Hind
        intro Hfalse'
        simp [Hfalse'] at Hp
      contradiction

theorem course_pairs_disjoint (ps qs : Finset Member):
  ∀ c d, c ≠ d → Disjoint (course_pairs c ps) (course_pairs d qs) :=
by
  intros c d Hneq
  induction ps using Finset.induction_on
  case empty => simp [course_pairs]
  case insert e ps _ Hind =>
    rw [@course_pairs_insert]
    simp
    constructor
    · exact course_pairs_notmem d c qs (id (Ne.symm Hneq)) e
    assumption

theorem course_pairs_sub (ps : Finset Member):
  ∀ c, ∀ p ∉ ps, course_pairs c ps ⊂ course_pairs c (ps ∪ {p}) :=
by
  intros c p Hp
  induction ps using Finset.induction_on
  case empty => simp [course_pairs]
  case insert d ps Hd Hind =>
    simp at Hp
    by_cases p = d
    case pos Heq =>
      simp [Heq] at Hp
    case neg Hneq =>
      simp [Hneq] at Hp
      simp [Hneq]
      have Hind' := Hind Hp
      rw [@course_pairs_insert]
      rw [@course_pairs_insert]
      apply Finset_ssubset_insert
      · assumption
      · apply course_pairs_notmem'
        intro Hfalse
        simp at Hfalse
        cases Hfalse
        case _ _ => contradiction
        case _ Heq => rw [Heq] at Hneq
                      contradiction

theorem course_pairs_mem₁:
  cp ∈ course_pairs c ps → cp.1 = c :=
by
  induction ps using Finset.induction_on
  case empty => simp [course_pairs]
  case insert p ps _s Hind =>
    rw [@course_pairs_insert]
    simp
    intro Hcp
    cases Hcp
    case inl Hcp =>
      simp [Hcp]
    case inr Hcp =>
      exact Hind Hcp

theorem course_pairs_mem₂:
  cp ∈ course_pairs c ps → cp.2 ∈ ps :=
by
  induction ps using Finset.induction_on
  case empty => simp [course_pairs]
  case insert p ps _ Hind =>
    simp
    rw [@course_pairs_insert]
    simp
    intro Hcp
    cases Hcp
    case inl Hcp =>
      left
      simp [Hcp]
    case inr Hcp =>
      right
      exact Hind Hcp

def all_pairs (cs : Finset Course) (attns : Course → Finset Member) : Finset (Course × Member) :=
  cs.fold Union.union ∅ (fun x => course_pairs x (attns x))

theorem all_pairs_insert (cs : Finset Course) (attns : Course → Finset Member):
  ∀ c, all_pairs (insert c cs) attns = course_pairs c (attns c) ∪ all_pairs cs attns :=
by
  intro c
  simp [all_pairs]

theorem all_pairs_notmem_disjoint (cs : Finset Course) (attns : Course → Finset Member):
  ∀ c ∉ cs, Disjoint (course_pairs c (attns c)) (all_pairs cs attns) :=
by
  induction cs using Finset.induction_on
  case empty => simp [all_pairs]
  case insert d cs _ Hind =>
    simp
    intros c Hc
    by_cases c = d
    case pos Heq =>
      simp [Heq] at Hc
    case neg Hneq =>
      simp [Hneq] at Hc
      simp [all_pairs]
      constructor
      · exact course_pairs_disjoint (attns c) (attns d) c d Hneq
      exact Hind c Hc

theorem all_pairs_notmem_disjoint' (cs : Finset Course) (attns : Course → Finset Member):
  ∀ c, ∀ d ∉ cs, Disjoint (course_pairs d (attns d)) (all_pairs cs (fun c' => if c' = c then attns c' ∪ {p} else attns c')) :=
by
  intro e
  induction cs using Finset.induction_on
  case empty => simp [all_pairs]
  case insert d cs _ Hind =>
    simp
    intros c Hc
    by_cases c = d
    case pos Heq =>
      simp [Heq] at Hc
    case neg Hneq =>
      simp [Hneq] at Hc
      simp [all_pairs]
      constructor
      · exact course_pairs_disjoint (attns c) (if d = e then attns d ∪ {p} else attns d) c d Hneq
      exact Hind c Hc

theorem all_pairs_notmem_disjoint'' (cs : Finset Course) (attns : Course → Finset Member):
  ∀ c ∉ cs, Disjoint (course_pairs c (attns c ∪ {p})) (all_pairs cs attns) :=
by
  induction cs using Finset.induction_on
  case empty => simp [all_pairs]
  case insert d cs _ Hind =>
    simp
    intros c Hc
    by_cases c = d
    case pos Heq =>
      simp [Heq] at Hc
    case neg Hneq =>
      simp [Hneq] at Hc
      simp [all_pairs]
      constructor
      · exact course_pairs_disjoint (attns c ∪ {p}) (attns d) c d Hneq
      exact Hind c Hc

theorem all_pairs_insert_mem (cs : Finset Course) (attns : Course → Finset Member):
  ∀ c ∈ cs, all_pairs (insert c cs) attns = all_pairs cs attns :=
by
  -- Note : induction is not needed ... case analysis ?
  induction cs using Finset.induction_on
  case empty => simp
  case insert d cs Hd _ =>
    intros c Hc
    simp [Hd] at Hc
    cases Hc
    case inl Hc =>
      simp [←Hc]
    case inr Hc =>
      simp [Hc]

theorem all_pairs_attns_notmem (cs : Finset Course) (attns : Course → Finset Member):
  ∀ c ∉ cs, all_pairs cs (fun c' => if c' = c then attns c' ∪ {p} else attns c')
            = all_pairs cs (fun c' => attns c') :=
by
  intros c Hc
  induction cs using Finset.induction_on
  case empty => simp [all_pairs]
  case insert d cs _ Hind =>
    simp at Hc
    by_cases c = d
    case pos Heq =>
      simp [←Heq] at Hc
    case neg Hneq =>
      simp [Hneq] at Hc
      rw [all_pairs_insert]
      rw [Hind Hc]
      rw [all_pairs_insert]
      split
      case inl Heq =>
        rw [Heq] at Hneq
        contradiction
      case inr Hneq' =>
        rfl

theorem all_pairs_mem₁ (cs : Finset Course) (attns : Course → Finset Member):
  ∀ cp ∈ all_pairs cs attns, cp.1 ∈ cs :=
by
  intros cp Hcp
  induction cs using Finset.induction_on
  case empty => simp [all_pairs] at Hcp
  case insert d cs _ Hind =>
    simp
    rw [all_pairs_insert] at Hcp
    by_cases cp.1 = d
    case pos Heq =>
      simp [Heq]
    case neg Hneq =>
      right
      apply Hind
      have Hncp: cp ∉ course_pairs d (attns d) := by
        apply course_pairs_notmem
        intro Hfalse
        rw [Hfalse] at Hneq
        contradiction
      simp [Hncp] at Hcp
      assumption

theorem all_pairs_mem₂ (cs : Finset Course) (attns : Course → Finset Member):
  ∀ cp ∈ all_pairs cs attns, cp.2 ∈ attns cp.1 :=
by
  intros cp Hcp
  induction cs using Finset.induction_on
  case empty => simp [all_pairs] at Hcp
  case insert d cs _ Hind =>
    rw [all_pairs_insert] at Hcp
    simp at Hcp
    by_cases cp.1 = d
    case pos Heq =>
      cases Hcp
      case inl Hcp =>
        apply course_pairs_mem₂ (c:=cp.1)
        simp [Heq, Hcp]
      case inr Hcp =>
        exact Hind Hcp
    case neg Hneq =>
      cases Hcp
      case inl Hcp =>
        have Hcontra: cp ∉ course_pairs d (attns d) := by
          apply course_pairs_notmem
          intro Hcontra
          simp [Hcontra] at Hneq
        contradiction
      case inr Hcp =>
        exact Hind Hcp

def all_members (cs : Finset Course) (attns : Course → Finset Member) :=
  cs.fold Union.union ∅ (fun x => attns x)

theorem all_pairs_members:
  ∀ cp ∈ all_pairs cs attns, cp.2 ∈ all_members cs attns :=
by
  intros cp Hcp
  induction cs using Finset.induction_on
  case empty => simp [all_pairs] at Hcp
  case insert d cs _ Hind =>
    simp [all_members]
    rw [all_pairs_insert] at Hcp
    simp at Hcp
    cases Hcp
    case inl Hcp =>
      left
      exact course_pairs_mem₂ Hcp
    case inr Hcp =>
      right
      simp [all_members] at Hind
      apply Hind
      assumption

theorem all_pairs_lemma (cs : Finset Course) (attns : Course → Finset Member):
  ∀ c ∈ cs, ∀ p ∉ attns c,
    all_pairs cs attns ⊂ all_pairs cs (fun c' => if c' = c then attns c' ∪ {p} else attns c') :=
by
  intros c Hc p Hp
  induction cs using Finset.induction_on
  case empty => simp at Hc
  case insert d cs Hd Hind =>
    simp at Hc
    cases Hc
    case inl Hc =>
      simp [←Hc]
      simp [←Hc] at Hd
      rw [all_pairs_insert]
      rw [all_pairs_insert]
      simp
      rw [all_pairs_attns_notmem]
      · have H₁: all_pairs cs attns = all_pairs cs (fun c' => attns c') := by
          rfl
        rw [←H₁] ; clear H₁
        have H₂: course_pairs c (attns c) ⊂ course_pairs c (attns c ∪ {p}) := by
          exact course_pairs_sub (attns c) c p Hp
        rw [@Finset.union_comm]
        nth_rw 2 [@Finset.union_comm]
        apply Finset_ssubset_union_left
        · assumption
        · rw [@disjoint_comm]
          exact all_pairs_notmem_disjoint'' cs (fun c => attns c) c Hd
      · assumption
    case inr Hc =>
      rw [all_pairs_insert]
      rw [all_pairs_insert]
      by_cases d = c
      case pos Heq =>
        rw [Heq] at Hd
        contradiction
      case neg Hneq =>
        simp [Hneq]
        have Hind' := Hind Hc
        apply Finset_ssubset_union_left
        · assumption
        · exact all_pairs_notmem_disjoint' cs (fun ⦃d⦄ => attns d) c d Hd


def variant (m2 : M2 ctx) :=
  (Finset.card ctx.availableCourses * Finset.card ctx.participants)
  - (all_pairs m2.domain m2.attendants).card

theorem PO_convergence (m2 : M2 ctx) (p : Member) (c : Course) :
  Machine.invariant m2
  → guard m2 p c
  → variant (action m2 p c) < variant m2 :=
by
  intros Hinv Hgrd
  simp [guard] at Hgrd
  simp [variant]
  apply Nat.sub_lt_sub_left
  · simp [Machine.invariant] at Hinv
    obtain ⟨Hinv₁, _, _, Hinv₄, _⟩ := Hinv
    simp [invariant₁] at Hinv₁
    simp [invariant₄] at Hinv₄
    rw [← @Finset.card_product]
    have H₁: ∀ cp ∈ all_pairs m2.domain m2.attendants, cp.1 ∈ ctx.availableCourses := by
      have H₁: ∀ cp ∈ all_pairs m2.domain m2.attendants, cp.1 ∈ m2.domain := by
        exact fun cp a => all_pairs_mem₁ m2.domain m2.attendants cp a
      exact fun cp a => Hinv₁ (H₁ cp a)
    have H₂: ∀ cp ∈ all_pairs m2.domain m2.attendants, cp.2 ∈ ctx.participants := by
      have H₂: ∀ cp ∈ all_pairs m2.domain m2.attendants, cp.2 ∈ m2.attendants cp.1 := by
        exact fun cp a => all_pairs_mem₂ m2.domain m2.attendants cp a
      exact fun cp a => Hinv₄ cp.1 (H₂ cp a)
    have H₃: all_pairs m2.domain m2.attendants ⊆ ctx.availableCourses ×ˢ ctx.participants := by
      apply Finset_subset_product_of_subsets
      · apply H₁
      · apply H₂
    have H₄: all_pairs m2.domain m2.attendants ⊂ ctx.availableCourses ×ˢ ctx.participants := by
      apply Finset_ssubset_of_subset
      · assumption
      · exists (c,p)
        constructor
        · simp
          constructor
          · apply Hinv₁ Hgrd.left
          apply Hgrd.right.right.left
        intro Hfalse
        have H₄: p ∈ m2.attendants c := by
          apply all_pairs_mem₂ (cp:=(c,p)) (cs:=m2.domain)
          · assumption
        simp [Hgrd] at H₄
    exact Finset.card_lt_card H₄
  · apply Finset.card_lt_card
    apply all_pairs_lemma <;> simp [Hgrd]

theorem PO_strengthening (m2 : M2 ctx):
  Machine.invariant m2 →
  Register.guard m2 p c →
    ∀ (m1 : M1 ctx.toContext_1),
      Refinement.refine m2 m1
      → M1.Register.guard m1 p c :=
by
  intros Hinv Hgrd m1 Href
  simp [Machine.invariant] at Hinv
  simp [Refinement.refine] at Href
  obtain ⟨Href₁, _, Href₃⟩ := Href
  simp [refine₁] at Href₁
  obtain ⟨Hgrd₁, Hgrd₂, Hgrd₃, Hgrd₄⟩ := Hgrd
  simp [M1.Register.guard]
  constructor
  · rw [←Href₁]
    assumption
  constructor
  · assumption
  constructor
  · intro Hfalse
    contradiction
  simp [M1.Register.unregistered?]
  simp [refine₃] at Href₃
  intro Hfalse
  have ⟨_, H₂⟩ := Href₃ c p Hfalse
  contradiction

theorem PO_simulation (m2: M2 ctx):
  Machine.invariant m2 →
  Register.guard m2 p c →
    ∀ (m1 : M1 ctx.toContext_1),
      Refinement.refine m2 m1 →
        Refinement.refine (Register.action m2 p c) (M1.Register.action m1 p c) :=
by
  simp [Refinement.refine]
  intros _ Hgrd₁ _ _ _ m1 Href₁ Href₂ Href₃
  simp [M1.Register.action]
  constructor
  · simp [refine₁] at Href₁
    simp [refine₁, Href₁]
  constructor
  · simp [refine₂] at Href₂
    simp [refine₂]
    intros c' Hc' p' Hp'
    by_cases c'= c
    case pos Heq =>
      simp [Heq]
      simp [Heq] at Hp'
      cases Hp'
      case inl Hp' =>
        right
        apply Href₂ <;> assumption
      case inr Hp' =>
        simp [Hp']
    case neg Hneq =>
      simp [Hneq] at Hp'
      right
      apply Href₂ <;> assumption
  -- refine₃
  simp [refine₃] at Href₃
  simp [refine₃]
  rintro c' p' ⟨Hc', Hp'⟩
  · simp [Hc', Hp'] ; assumption
  case _ Hcp' =>
    have ⟨Href₃', Href₃''⟩ := Href₃ c' p' Hcp'
    simp [Href₃']
    by_cases c' = c
    case pos Heq =>
      simp [Heq]
      left
      simp [Heq] at Href₃''
      assumption
    case neg Hneq =>
      simp [Hneq]
      assumption

end Register

def Register : RConvergentEvent Nat (M1 ctx.toContext_1) (M2 ctx) (Member × Course) (Member × Course) :=
  newRConvergentEvent {
    guard := fun m (p,c) => Register.guard m p c
    action := fun m (p,c) => Register.action m p c
    safety := fun m (p,c) => by simp [Machine.invariant, Register.guard]
                                intros
                                constructor
                                · apply Register.PO_safety₁ ; assumption
                                constructor
                                · apply Register.PO_safety₂ ; assumption
                                constructor
                                · apply Register.PO_safety₃ <;> assumption
                                constructor
                                · apply Register.PO_safety₄ <;> assumption
                                apply Register.PO_safety₅ <;> assumption

    variant := Register.variant
    convergence := fun m (p,c) => Register.PO_convergence m p c
    absParam := id
    abstract := M1.Register.toEvent
    strengthening := fun m (p,c) => by simp
                                       apply Register.PO_strengthening
    simulation := fun m (p,c) => by simp
                                    apply Register.PO_simulation
  }

-/

end M2


end CoursesSpec
