
import «LeanMachines»
import «LeanMachines».Examples.Buffer.Buffer0

open Buffer







class DecidableEvent [Machine ctx M] (ev : Event M α β ) where
  hdecide : ∀ (m : M) (x : α), Decidable (ev.guard m x)

instance instPutDec : DecidableEvent
  B0.Put.toEvent
  (M := B0 ctx)
where
  hdecide m _ := m.size.decLt ctx.maxSize


instance Decidable_from_hdecide [Machine ctx M] (ev : Event M α β)
  (hdecide :∀ (m : M) (x : α), Decidable (ev.guard m x)) : DecidableEvent ev
where
  hdecide := hdecide

#check Decidable_from_hdecide B0.Put.toEvent


def main : IO Unit :=
do
  let b0 : Buffer.B0 ⟨5,by omega⟩ := Prod.snd $ B0.Init.init () (trivial)
  let grd' := decide  (B0.Put.guard b0 ()) (h := b0.size.decLt 5)
  -- let grd' := Event.guard_to_bool B0.Put.toEvent b0 () (B0.Put_deci b0)
  let b0 : B0 ⟨5, by omega⟩ :=
  by
    by_cases grd' = true
    case pos Hpos =>
      let r := Prod.snd $ B0.Put.action b0 ()
        (by
          exact of_decide_eq_true (inst :=
            (Decidable_from_hdecide B0.Put.toEvent
            (λ m _ =>
              by
                simp[B0.Put]
                exact m.size.decLt 5)).hdecide b0 ())
            (Hpos)
        )
      exact r
    case neg Hneg => exact b0

  -- let b0 : B0 ⟨5,by omega⟩ := by -- Non computable! !
  --   by_cases B0.Put.guard b0 ()
  --   case pos Hpos => exact Prod.snd $ B0.Put.action b0 () (Hpos)
  --   case neg Hneg => exact b0

  IO.println s!"b0.size après exec :{b0.size}"
  -- let input ← IO.rand 0 7
  -- for i in [0...input] do
  --   if B0.Put.guard b0 ()
  --     then
  --       let b0 := Prod.snd $ B0.Put.action b0 () (by sorry)
  --       IO.println s!"B0 contient v.{b0.size}"
  --     else

  IO.println s!"Lean Machines v.{LeanMachines.VERSION_MAJ}.{LeanMachines.VERSION_MIN}.{LeanMachines.VERSION_REV} {LeanMachines.VERSION_STS}"
  IO.println "fin du petit exemple !"
