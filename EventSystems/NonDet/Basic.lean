
import EventSystems.Classes
import EventSystems.Basic

structure _NDEvent (M) [Machine CTX M] (α) (β : Type)
  extends _EventRoot M α where

  effect: M → α → (β × M) → Prop

def _NDEvent_fromEvent [Machine CTX M] (ev : _Event M α β) : _NDEvent M α β :=
{
  guard := ev.guard
  effect := fun m x (x'', m'') => let (x', m') := ev.action m x
                                  m'' = m' ∧ x'' = x'
}

-- The functor instance is existential, not suprising given the relational context
instance [Machine CTX M] : Functor (_NDEvent M γ) where
  map f ev :=
  {
    guard := ev.guard
    effect := fun m x (y, m') => ∃ z, ∃ m'', ev.effect m x (z, m'')
                                             ∧ y = f z ∧ m' = m''
  }

instance [Machine CTX M] : LawfulFunctor (_NDEvent M γ) where
  map_const := rfl
  id_map ev := by simp [Functor.map]
                  cases ev
                  case mk evr eff =>
                    simp
                    funext m x (y,m')
                    apply propext
                    constructor
                    · intro Hz
                      cases Hz
                      case _ z H =>
                        simp at H
                        simp [H]
                    intro Heff
                    simp
                    exists y

  comp_map g h ev := by simp [Functor.map]
                        funext m x (y,m')
                        apply propext
                        constructor
                        · intro Hz
                          cases Hz
                          case _ z H =>
                            simp at H
                            simp
                            exists (g z)
                            constructor
                            · exists z
                              simp [H]
                            simp [H]
                        simp
                        intros z t Heff Heq₁ Heq₂
                        exists t
                        simp [Heff, Heq₁, Heq₂]


-- There are two possible, distinct contravariant functors
-- for non-deterministic events.

-- The first operates on the output, hence it cannot be use
-- in a profunctor context
instance [Machine CTX M] : Contravariant (_NDEvent M γ) where
  contramap f ev :=
  {
    guard := ev.guard
    effect := fun m x (y, m') => ev.effect m x ((f y), m')
  }

instance [Machine CTX M] : LawfullContravariant (_NDEvent M β) where
  cmap_id _ := rfl
  cmap_comp _ _ := rfl

-- The second operates on the input
abbrev _CoNDEvent (M) [Machine CTX M] (α) (β) := _NDEvent M β α

@[simp]
def CoNDEvent_from_NDEvent [Machine CTX M] (ev : _NDEvent M α β) : _CoNDEvent M β α :=
 ev

@[simp]
def NDEvent_from_CoNDEvent [Machine CTX M] (ev : _CoNDEvent M β α) : _NDEvent M α β :=
 ev


instance [Machine CTX M] : Contravariant (_CoNDEvent M γ) where
  contramap f ev :=
  {
     guard := fun m x => ev.guard m (f x)
     effect := fun m x (y, m')  => ev.effect m (f x) (y, m')
  }

instance [Machine CTX M] : LawfullContravariant (_CoNDEvent M γ) where
  cmap_id _ := rfl
  cmap_comp _ _ := rfl

-- There is a unique possible profunctor instance
instance [Machine CTX M] : Profunctor (_NDEvent M) where
  dimap {α β} {γ δ} (f : β → α) (g : γ → δ) (ev : _NDEvent M α γ) : _NDEvent M β δ :=
  let ev' := NDEvent_from_CoNDEvent (Contravariant.contramap f (CoNDEvent_from_NDEvent ev))
  g <$> ev'

instance [Machine CTX M] : LawfulProfunctor (_NDEvent M) where
  dimap_id := by simp [Profunctor.dimap, Contravariant.contramap]
                 exact fun {α β} => rfl
  dimap_comp f f' g g' := by simp [Profunctor.dimap, Contravariant.contramap, Functor.map]
                             funext ev
                             simp
                             funext m x (y,m')
                             simp
                             constructor
                             · intro Heff
                               cases Heff
                               case _ u Heff =>
                                 exists (g' u)
                                 simp [Heff]
                                 exists u
                                 simp [Heff]
                             intro Heff
                             cases Heff
                             case _ t Heff =>
                               simp at Heff
                               cases Heff
                               case _ Heff Hy =>
                                 cases Heff
                                 case _ u Heff =>
                                   exists u
                                   simp [Heff, Hy]

instance [Machine CTX M] : StrongProfunctor (_NDEvent M) where
  first' {α β γ} (ev : _NDEvent M α β): _NDEvent M (α × γ) (β × γ) :=
    {
      guard := fun m (x, _) => ev.guard m x
      effect := fun m (x,u) ((y, v), m') => v = u ∧ ev.effect m x (y, m')
    }

instance [Machine CTX M] : LawfulStrongProfunctor (_NDEvent M) where
