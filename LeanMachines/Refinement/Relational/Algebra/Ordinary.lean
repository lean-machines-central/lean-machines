import LeanMachines.Event.Prelude
import LeanMachines.Event.Basic
import LeanMachines.Event.Algebra.Basic
import LeanMachines.Event.Algebra.Ordinary
import LeanMachines.Algebra.Contravariant
import LeanMachines.Algebra.Profunctor
import LeanMachines.Algebra.Arrow
import LeanMachines.Event.Ordinary
import LeanMachines.Refinement.Relational.Basic
import LeanMachines.Refinement.Relational.Ordinary

import LeanMachines.NonDet.Algebra.Ordinary
import LeanMachines.NonDet.Ordinary
import LeanMachines.Refinement.Relational.NonDet.Ordinary

#check OrdinaryREvent


instance RefinementMap [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (abs : OrdinaryEvent AM α' β')
  (ev : OrdinaryREvent AM M abs α β)
  (f : β → γ)
  (f' : β' → γ')
  (lift_f : γ → γ')
  (hlift :  ∀ x : β, lift_f (f x) = f' (ev.lift_out x))
  :
  SafeREventPO
    ((f <$> (ev.toOrdinaryEvent)).toEvent) ((f' <$> abs).toEvent)
    (instSafeAbs := instSafeEventPO_OrdinaryEvent (f' <$> abs))
    (instSafeEv := instSafeEventPO_OrdinaryEvent (f <$> ev.toOrdinaryEvent))
    (valid_kind := by simp)
  where
    lift_in := ev.lift_in
    lift_out := lift_f
    strengthening := ev.strengthening
    simulation m x hinv hgrd am Href :=
      by
        simp[Functor.map,map_Event,_root_.mapEvent]
        constructor
        · have h := (ev.simulation m x hinv hgrd am Href).1
          specialize hlift (ev.toOrdinaryEvent.2 m x hgrd).fst
          rw[hlift]
          rw[h]
        · exact (ev.simulation m x hinv hgrd am Href).2


instance RefinementDimap [Machine ACTX AM] [Machine CTX M] [instR : Refinement AM M]
  (abs : OrdinaryEvent AM α' β')
  (ev : OrdinaryREvent AM M abs α β)
  (f : β → γ)
  (f' : β'→ γ')
  (g : δ → α)
  (g' : δ'→ α')
  (lift_f : γ → γ')
  (hlift_f : ∀ x : β, lift_f (f x) = f' (ev.lift_out x))
  (lift_g : δ → δ')
  (hlift_g : ∀ x : δ, g' (lift_g x) = ev.lift_in (g x))
  :
  SafeREventPO
    (M := M)
    (AM := AM)
    (Profunctor.dimap g f ev.toOrdinaryEvent).toEvent (Profunctor.dimap g' f' abs).toEvent
    (instSafeEv := instSafeEventPO_OrdinaryEvent (Profunctor.dimap g f ev.toOrdinaryEvent))
    (instSafeAbs := instSafeEventPO_OrdinaryEvent (Profunctor.dimap g' f' abs))
    (valid_kind := by simp)
  where
    lift_in := lift_g
    lift_out := lift_f
    strengthening m x :=
      by
        simp[Profunctor.dimap]
        specialize hlift_g x
        rw[hlift_g]
        exact (ev.strengthening m (g x))
    simulation m x hinv hgrd am Href :=
      by
        simp[Profunctor.dimap,map_Event,_root_.mapEvent]
        constructor
        ·
          have h := (ev.simulation m (g x) hinv hgrd am Href).1
          specialize hlift_f (ev.toOrdinaryEvent.2 m (g x) hgrd).fst
          rw[hlift_f]
          specialize hlift_g x
          simp[hlift_g]
          rw[h]
        · specialize hlift_g x
          simp[hlift_g]
          exact (ev.simulation m (g x) hinv hgrd am Href).2




instance RefinementDimap'[Machine ACTX AM] [Machine CTX M] [instR : Refinement AM M]
  (abs : OrdinaryEvent AM α' β')
  (ev : OrdinaryREvent AM M abs α β)
  (f : β → γ)
  (f' : γ → β')
  (g : δ → α)
  (g' : δ→ α')
  (hlift_g : g' = ev.lift_in ∘ g)
  (hlift_f : ev.lift_out = f' ∘ f)
  :
  SafeREventPO
    (M := M)
    (AM := AM)
    (Profunctor.dimap g f ev.toOrdinaryEvent).toEvent abs.toEvent
    (instSafeEv := instSafeEventPO_OrdinaryEvent (Profunctor.dimap g f ev.toOrdinaryEvent))
    (instSafeAbs := instSafeEventPO_OrdinaryEvent abs)
    (valid_kind := by simp)
  where
    lift_in := g'
    lift_out := f'
    strengthening m x :=
    by
      simp[Profunctor.dimap]
      rw[hlift_g]
      have h := (ev.strengthening m (g x))
      exact h
    simulation m x hinv hgrd am Href :=
      by
        simp[Profunctor.dimap]
        constructor
        ·
          have h := (ev.simulation m (g x) hinv hgrd am Href).1
          have h' : ∀x, ev.lift_out x = f' (f x) :=
          by
            exact fun x => congrFun hlift_f x
          specialize h' ((ev.toOrdinaryEvent.2 m (g x) hgrd).1)
          rw[←h']
          simp[hlift_g]
          exact h
        · simp[hlift_g]
          exact (ev.simulation m (g x) hinv hgrd am Href).2

instance RefinementCategory [Machine ACTX AM] [Machine CTX M][instR : Refinement AM M]
  (abs₁ : OrdinaryEvent AM α' β')
  (abs₂ : OrdinaryEvent AM β' γ')
  (ev₁ : OrdinaryREvent AM M abs₁ α β)
  (ev₂  : OrdinaryREvent AM M abs₂ β γ)
  (hseq : ∀ x : β, ev₁.lift_out x = ev₂.lift_in x)
  : SafeREventPO
  (M := M)
  (AM := AM)
  (ev₁.toOrdinaryEvent (>>>) ev₂.toOrdinaryEvent).toEvent (abs₁ (>>>) abs₂).toEvent
  (instSafeEv :=  instSafeEventPO_OrdinaryEvent (ev₁.toOrdinaryEvent (>>>) ev₂.toOrdinaryEvent))
  (instSafeAbs :=  instSafeEventPO_OrdinaryEvent (abs₁ (>>>) abs₂))
  (valid_kind := simp)
  where
    lift_in := ev₁.lift_in
    lift_out := ev₂.lift_out
    strengthening m x hinv :=
    by
      simp[Category.comp]
      intros hgrd₁ hgrd₂ am href
      specialize hgrd₂ hgrd₁
      constructor
      · exact ev₁.strengthening m x hinv hgrd₁ am href
      · intro hgabs₁
        have h := ev₂.strengthening
        let om' := (ev₁.toOrdinaryEvent.2 m x hgrd₁)
        specialize h (om'.2) om'.1
        have hyp := ev₁.simulation m x hinv hgrd₁ am href
        simp at hyp
        have ⟨hyp₁,hyp₂⟩ := hyp
        rw[←hyp₁]
        unfold om' at h
        have hsafe := ev₁.safety m x hinv hgrd₁
        specialize h hsafe hgrd₂ (abs₁.2  am (ev₁.lift_in x) (ev₁.strengthening m x hinv hgrd₁ am href) ).2
        specialize hseq (ev₁.toOrdinaryEvent.2 m x hgrd₁).1
        rw[hseq]
        apply h
        assumption
    simulation m x hinv :=
      by
        simp[Category.comp]
        intros Hgrd am Href
        have hsim₁ := ev₁.simulation m x hinv Hgrd.1 am Href
        simp at hsim₁
        have hsim₂ := ev₂.simulation (ev₁.action m x Hgrd.1).2 (ev₁.action m x Hgrd.1).1
        specialize hsim₂ (ev₁.safety m x hinv Hgrd.1) (Hgrd.2 Hgrd.1)
        specialize hsim₂ (abs₁.2 am (ev₁.lift_in x) (ev₁.strengthening m x hinv Hgrd.1 am Href)).2
        specialize hsim₂ hsim₁.2
        simp at hsim₂
        have ⟨lhsim₂,rhsim₂⟩ := hsim₂
        have ⟨lhsim₁,rhsim₁⟩ := hsim₁
        clear hsim₂ hsim₁
        have hsequence := hseq (ev₁.action m x Hgrd.1).1
        constructor
        · rw[lhsim₂]
          rw[hsequence] at lhsim₁
          simp[lhsim₁]
        ·
          have h :
            (abs₁.action am (ev₁.lift_in x) (ev₁.strengthening m x hinv Hgrd.1 am Href)).1
            = (ev₂.lift_in (ev₁.action m x Hgrd.1).1)
            :=
            by
              rw[←hsequence]
              rw[←lhsim₁]
          simp[h]
          assumption


instance RefinementSplit[Machine ACTX AM] [Machine CTX M][instR : Refinement AM M]
  (abs₁ : OrdinaryEvent AM α' β')
  (abs₂ : OrdinaryEvent AM γ' δ')
  (ev₁ : OrdinaryREvent AM M abs₁ α β)
  (ev₂  : OrdinaryREvent AM M abs₂ γ δ)
  : SafeREventPO
  (M := M)
  (AM := AM)
  (Arrow.split ev₁.toOrdinaryEvent ev₂.toOrdinaryEvent).toEvent (Arrow.split abs₁ abs₂).toEvent
  (instSafeEv :=  instSafeEventPO_OrdinaryEvent (Arrow.split ev₁.toOrdinaryEvent ev₂.toOrdinaryEvent))
  (instSafeAbs :=  instSafeEventPO_OrdinaryEvent (Arrow.split abs₁ abs₂))
  (valid_kind := simp)
  where
    lift_in := λ (x,y) => (ev₁.lift_in x, ev₂.lift_in y)
    lift_out := λ (x,y) => (ev₁.lift_out x, ev₂.lift_out y)
    strengthening m x hinv :=
    by
      simp[Arrow.split]
      intros hgrd₁ hgrd₂ am href
      have hst₁ := ev₁.strengthening m x.1 hinv
      have hst₂ := ev₂.strengthening ((ev₁.action m x.1 hgrd₁).2) x.2 (ev₁.safety m x.1 hinv hgrd₁)
      apply (And.intro (hst₁ hgrd₁ am href))
      intro hgrd_abs₁
      specialize hst₂ (hgrd₂ hgrd₁) (abs₁.action am (ev₁.lift_in x.1) hgrd_abs₁).2
      apply hst₂
      exact (ev₁.simulation m x.1 hinv hgrd₁ am href).2
    simulation m x hinv :=
    by
      simp[Arrow.split]
      intros Hgrd am Href
      have hsim₂ :=
          ev₂.simulation
            ((ev₁.action m x.1 Hgrd.1).2) x.2
            (ev₁.safety m x.1 hinv Hgrd.1) (Hgrd.2 Hgrd.1)
            (abs₁.action am (ev₁.lift_in x.1) (ev₁.strengthening m x.1 hinv Hgrd.1 am Href)).2
            (ev₁.simulation m x.1 hinv Hgrd.1 am Href).2
      simp at hsim₂
      repeat (apply And.intro)
      · exact (ev₁.simulation m x.1 hinv Hgrd.1 am Href).1
      · exact hsim₂.1
      · exact hsim₂.2



instance RefinementSplitIn [Machine ACTX AM] [Machine CTX M][instR : Refinement AM M]
  (abs₁ : OrdinaryEvent AM α' β')
  (abs₂ : OrdinaryEvent AM γ' δ')
  (ev₁ : OrdinaryREvent AM M abs₁ α β)
  (ev₂  : OrdinaryREvent AM M abs₂ γ δ)
  : SafeREventPO
  (M := M)
  (AM := AM)
  (ArrowChoice.splitIn ev₁.toOrdinaryEvent ev₂.toOrdinaryEvent).toEvent (ArrowChoice.splitIn abs₁ abs₂).toEvent
  (instSafeEv :=  instSafeEventPO_OrdinaryEvent (ArrowChoice.splitIn ev₁.toOrdinaryEvent ev₂.toOrdinaryEvent))
  (instSafeAbs :=  instSafeEventPO_OrdinaryEvent (ArrowChoice.splitIn abs₁ abs₂))
  (valid_kind := simp)
  where
    lift_in := λ x => match x with | .inl l => Sum.inl $ ev₁.lift_in l | .inr r => Sum.inr $ ev₂.lift_in r
    lift_out := λ x => match x with | .inl l => Sum.inl $ ev₁.lift_out l | .inr r => Sum.inr $ ev₂.lift_out r
    strengthening m x hinv :=
    by
      simp[ArrowChoice.splitIn,altOrdinaryEvent]
      cases x
      case inl l =>
        exact ev₁.strengthening m l hinv
      case inr r =>
        exact ev₂.strengthening m r hinv
    simulation m x hinv :=
    by
      simp[ArrowChoice.splitIn,altOrdinaryEvent]
      intros Hgrd am Href
      cases x
      case inl l =>
        simp at Hgrd
        simp
        exact ev₁.simulation m l hinv Hgrd am Href
      case inr r =>
        simp at Hgrd
        simp
        exact ev₂.simulation m r hinv Hgrd am Href


instance RefinementNDMap [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (abs : OrdinaryNDEvent AM α' β')
  (ev : OrdinaryRNDEvent AM M α β α' β' abs)
  (f : β → γ)
  (f' : β' → γ')
  (lift_f : γ → γ')
  (hlift :  ∀ x : β, lift_f (f x) = f' (ev.lift_out x))
  :
  SafeRNDEventPO
    ((f <$> (ev.toOrdinaryNDEvent)).toNDEvent) ((f' <$> abs).toNDEvent)
    (instSafeAbs := instSafeNDEventPO_Ordinary (f' <$> abs))
    (instSafeEv := instSafeNDEventPO_Ordinary (f <$> ev.toOrdinaryNDEvent))
    (valid_kind := by simp)
  where
    lift_in := ev.lift_in
    lift_out := lift_f
    strengthening := ev.strengthening
    simulation m x hinv hgrd y m' :=
    by
      simp[Functor.map,map_Event,_root_.mapEvent]
      intros yβ hef heqyyβ am Href
      have ⟨am',h⟩ := (ev.simulation m x hinv hgrd yβ m' hef am Href)
      exists am'
      constructor
      · have hz := hlift yβ
        exists (ev.lift_out yβ)
        constructor
        · exact h.1
        · rw[heqyyβ]
          exact hz
      · exact h.2


instance RefinementNDDimap [Machine ACTX AM] [Machine CTX M] [instR : Refinement AM M]
  (abs : OrdinaryNDEvent AM α' β')
  (ev :  OrdinaryRNDEvent AM M α β α' β' abs)
  (f : β → γ)
  (f' : β'→ γ')
  (g : δ → α)
  (g' : δ'→ α')
  (lift_f : γ → γ')
  (hlift_f : ∀ x : β, lift_f (f x) = f' (ev.lift_out x))
  (lift_g : δ → δ')
  (hlift_g : ∀ x : δ, g' (lift_g x) = ev.lift_in (g x))
  :
  SafeRNDEventPO
    (M := M)
    (AM := AM)
    (Profunctor.dimap g f ev.toOrdinaryNDEvent).toNDEvent (Profunctor.dimap g' f' abs).toNDEvent
    (instSafeEv := instSafeNDEventPO_Ordinary (Profunctor.dimap g f ev.toOrdinaryNDEvent))
    (instSafeAbs := instSafeNDEventPO_Ordinary (Profunctor.dimap g' f' abs))
    (valid_kind := by simp)
  where
    lift_in := lift_g
    lift_out := lift_f
    strengthening m x :=
      by
        simp[Profunctor.dimap,Functor.map,ContravariantFunctor.contramap]
        specialize hlift_g x
        rw[hlift_g]
        exact ev.strengthening m (g x)

    simulation m x hinv hgrd y m':=
      by
        simp[Profunctor.dimap]
        simp only [Functor.map,map_Event,_root_.mapEvent]
        simp only [ContravariantFunctor.contramap]
        intros hef am Href
        replace ⟨yβ,m'',hef⟩ := hef
        have ⟨am',hyp⟩ := (ev.simulation m (g x) hinv hgrd yβ m'' hef.1 am Href)
        exists am'
        constructor
        · specialize hlift_g x
          specialize hlift_f yβ
          simp only[hlift_g]
          exists (ev.lift_out yβ)
          exists am'
          · constructor
            · exact hyp.1
            · constructor
              · rw[hef.2.1]
                exact hlift_f
              · rfl
        · rw[hef.2.2]
          exact hyp.2

instance RefinementNDCategory [Machine ACTX AM] [Machine CTX M][instR : Refinement AM M]
  (abs₁ : OrdinaryNDEvent AM α' β')
  (abs₂ : OrdinaryNDEvent AM β' γ')
  (ev₁ : OrdinaryRNDEvent AM M α β α' β' abs₁)
  (ev₂  : OrdinaryRNDEvent AM M β γ β' γ' abs₂)
  (hseq : ∀ x : β, ev₁.lift_out x = ev₂.lift_in x)
  : SafeRNDEventPO
  (M := M)
  (AM := AM)
  (ev₁.toOrdinaryNDEvent (>>>) ev₂.toOrdinaryNDEvent).toNDEvent (abs₁ (>>>) abs₂).toNDEvent
  (instSafeEv :=  instSafeNDEventPO_Ordinary (ev₁.toOrdinaryNDEvent (>>>) ev₂.toOrdinaryNDEvent))
  (instSafeAbs :=  instSafeNDEventPO_Ordinary (abs₁ (>>>) abs₂))
  (valid_kind := simp)
  where
    lift_in := ev₁.lift_in
    lift_out := ev₂.lift_out
    strengthening m x hinv :=
    by
      simp[Category.comp]
      intros hgrd₁ hgrd₂ am href
      constructor
      · exact ev₁.strengthening m x hinv hgrd₁ am href
      ·
        intro abs_grd₁
        intros y' am'
        intro hef₁
        specialize hgrd₂ hgrd₁
        have ⟨y,m',hef⟩ := ev₁.feasibility m x hinv hgrd₁
        specialize hgrd₂ y m' hef
        have ⟨am'',hsim₁⟩ := ev₁.simulation m x hinv hgrd₁ y m' hef am href
        have h := ev₂.strengthening m' y (ev₁.safety m x hinv hgrd₁ y m' hef) hgrd₂ am''
        have hyp : am'' = am' := by sorry
        have hyp' : ev₁.lift_out y = y' := by sorry
        rw[←hyp]
        rw[←hyp']
        rw[hseq y]
        apply h
        exact hsim₁.2
    simulation m x hinv hgrd y m':= sorry


instance RefinementNDSplit [Machine ACTX AM] [Machine CTX M][instR : Refinement AM M]
  [ParallelMachine M] [ParallelMachine AM]
  (abs₁ : OrdinaryNDEvent AM α' β')
  (abs₂ : OrdinaryNDEvent AM β' γ')
  (ev₁ : OrdinaryRNDEvent AM M α β α' β' abs₁)
  (ev₂  : OrdinaryRNDEvent AM M β γ β' γ' abs₂)
  : SafeRNDEventPO
  (M := M)
  (AM := AM)
  (Arrow.split ev₁.toOrdinaryNDEvent ev₂.toOrdinaryNDEvent).toNDEvent (Arrow.split abs₁ abs₂).toNDEvent
  (instSafeEv :=  instSafeNDEventPO_Ordinary (Arrow.split ev₁.toOrdinaryNDEvent ev₂.toOrdinaryNDEvent))
  (instSafeAbs :=  instSafeNDEventPO_Ordinary (Arrow.split abs₁ abs₂))
  (valid_kind := simp)
  where
    lift_in := λ (x,y) => (ev₁.lift_in x, ev₂.lift_in y)
    lift_out := λ (x,y) => (ev₁.lift_out x, ev₂.lift_out y)
    strengthening m x hinv :=
    by
      simp[Arrow.split]
      intros grd₁ grd₂ am href
      apply And.intro
        (ev₁.strengthening m x.1 hinv grd₁ am href)
        (ev₂.strengthening m x.2 hinv grd₂ am href)
    simulation m x hinv hgrd y m':=
    by
      simp[Arrow.split]
      intros m'' hef₁ m''' hef₂ hmul am href
      have ⟨y',am',hef_abs₁⟩ := abs₁.feasibility am (ev₁.lift_in x.1) (instR.refine_safe am m hinv href) (ev₁.strengthening m x.1 hinv hgrd.1 am href)
      have ⟨y'',am'',hef_abs₂⟩ := abs₂.feasibility am (ev₂.lift_in x.2) (instR.refine_safe am m hinv href) (ev₂.strengthening m x.2 hinv hgrd.2 am href)
      exists (am' * am'')
      constructor
      · exists am'
        have hyp : y' = ev₁.lift_out y.1 := by sorry
        have hyp' : y'' = ev₂.lift_out y.2 := by sorry
        rw[←hyp]
        apply And.intro hef_abs₁
        exists am''
        rw[←hyp']
        apply And.intro hef_abs₂ rfl
      · rw[hmul]

        sorry


-- instance RefinementNDSplitIn [Machine ACTX AM] [Machine CTX M][instR : Refinement AM M]
--   [ParallelMachine M] [ParallelMachine AM]
--   (abs₁ : OrdinaryNDEvent AM α' β')
--   (abs₂ : OrdinaryNDEvent AM β' γ')
--   (ev₁ : OrdinaryRNDEvent AM M α β α' β' abs₁)
--   (ev₂  : OrdinaryRNDEvent AM M β γ β' γ' abs₂)
--   : SafeRNDEventPO
--   (M := M)
--   (AM := AM)
--   (ArrowChoice.splitIn ev₁.toOrdinaryNDEvent ev₂.toOrdinaryNDEvent).toNDEvent (ArrowChoice.splitIn abs₁ abs₂).toNDEvent
--   (instSafeEv :=  instSafeNDEventPO_Ordinary (ArrowChoice.splitIn ev₁.toOrdinaryNDEvent ev₂.toOrdinaryNDEvent))
--   (instSafeAbs :=  instSafeNDEventPO_Ordinary (ArrowChoice.splitIn abs₁ abs₂))
--   (valid_kind := simp)
