import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary
import Lean.Data.AssocList
import Mathlib.Data.Finset.Basic


/-
  Utilities
-/


inductive IsElem : α → Lean.AssocList α β → Prop where
  | now : ∀ v : β, IsElem a (Lean.AssocList.cons a v xs)
  | later (a x : α) (b : β) (xs : Lean.AssocList α β):
    IsElem a xs →
      IsElem a (Lean.AssocList.cons x b xs)

def Lean.AssocList.search [DecidableEq α] (x : α) (xs : Lean.AssocList α β)
    (HIs : IsElem x xs) : β :=
    match xs with
    | Lean.AssocList.cons x' v xs' =>
    --On passe en mode tactique pour conserver la disjonction de cas sur x = x'
      by
        by_cases x = x'
        case pos _ => exact v
        case neg Hneg =>
          have HIs' : IsElem x xs' :=
            by
              cases HIs
              case now => contradiction
              case later h => assumption
          exact (Lean.AssocList.search x xs' HIs')




inductive Bank_State where
  | Init | Op | Trans
open Bank_State

structure Customer where
  id : String





structure Bank_Ctx where
  customers : List String
  accounts : Lean.AssocList String Nat
  axm_accounts : accounts ≠ Lean.AssocList.empty

structure Transfer where
  c_from : String
  c_to : String
  amount : Nat
  transferOK : Bool

structure Bank (ctx : Bank_Ctx) where
  bankState : Bank_State
  balance : Lean.AssocList String Nat
  transfer : Option Transfer

instance : Machine Bank_Ctx (Bank ctx) where
  context := ctx
  invariant m :=
    match m.transfer with
    | Option.none => True
    | Option.some t =>
      t.transferOK →
      Π (hf : IsElem t.c_from m.balance)
      , (t.c_from ≠ t.c_to ∧ t.amount ≤ Lean.AssocList.search t.c_from m.balance hf)




def Bank.Init : InitEvent (Bank ctx) Unit Unit :=
  newInitEvent''
  {
    init _ :=
    {
      bankState := Bank_State.Init
      , balance := ctx.accounts
      , transfer := none
    }
    safety _ :=
      by
        simp[Machine.invariant]
  }

def List.mem [BEq α] (x : α) (xs : List α) : Bool :=
  match xs.find? (λ e => x == e) with
  | none => false
  | some _ => true

def Bank.loginTrue : OrdinaryEvent (Bank ctx) String Bool :=
  newEvent
  {
    guard m x := ctx.customers.mem x ∧ m.bankState = Bank_State.Init
    action m x _ :=
      (
        true,
        {bankState := Bank_State.Op, balance := m.balance, transfer := m.transfer}
      )
    safety m x :=
    by
      simp[Machine.invariant]
      intros
      assumption
  }

def Bank.loginFalse : OrdinaryEvent (Bank ctx) String Bool :=
  newEvent
  {
    guard m x := !ctx.customers.mem x ∧ m.bankState = Bank_State.Init
    action m x _ :=
      (
        false,
        m
      )
    safety m x :=
    by
      simp[Machine.invariant]
      intros
      assumption
  }

def Bank.logOut : OrdinaryEvent (Bank ctx) Unit Unit :=
  newEvent''
  {
    guard m := m.bankState = Bank_State.Op
    action m _ :=
      {
        bankState := Bank_State.Init
        balance := m.balance
        transfer := m.transfer
      }
    safety :=
    by
      simp[Machine.invariant]
      intros
      assumption
  }


def Bank.transferRequest : OrdinaryEvent (Bank ctx) (String × String × Nat) Bool :=
newEvent
  {-- from x.1 to x.2.1 with a x.2.2 amount
    guard m x  := IsElem x.1 m.balance ∧ IsElem x.2.1 m.balance
    action m x hgrd :=
      let ok := m.balance.search x.1 hgrd.left ≥ x.2.2 ∧ x.1 ≠ x.2.1
      (
        ok,
        {
          bankState := Bank_State.Trans
          balance := m.balance
          transfer := some $ Transfer.mk x.1 x.2.1 x.2.2 ok
        }
      )
    safety m x :=
    by
      simp[Machine.invariant]
      intros hinv hgrd₁
      intros ok₁ ok₂ hf
      constructor
      · assumption
      · assumption -- works because of proof irrelevance !
  }

def findSome (o : Option α)
  (_ : match o with | none => False | some _ => True) : α :=
  match o with
  | some t => t

def Bank.transferExecTrue : OrdinaryEvent (Bank ctx) Unit Unit :=
newEvent''
{
  guard m := m.bankState = Bank_State.Trans ∧
    match m.transfer with
    | none => False
    | some t => t.transferOK ∧ IsElem t.c_from m.balance ∧ IsElem t.c_to m.balance
  action m hgrd :=
  let t := findSome m.transfer (α := Transfer)
    (
        by
          revert hgrd
          cases m.transfer
          case none =>
            simp
          case some t =>
            simp
      )
  let val_acc_from : Nat :=
    by
      revert hgrd
      cases m.transfer
      case none =>
        simp
        intro
        contradiction
      case some t =>
        simp
        intro h
        exact m.balance.search t.c_from (h.right.right.left)
  let val_acc_to : Nat :=
    by
      revert hgrd
      cases m.transfer
      case none =>
        simp
        intro
        contradiction
      case some t =>
        simp
        intro h
        exact m.balance.search t.c_to (h.right.right.right)
  let b' := m.balance.replace t.c_from (val_acc_from - t.amount)
  let b'':= b'.replace t.c_to (val_acc_to + t.amount)
  {
    bankState := Op
    transfer := none
    balance := b''
  }
  safety m :=
  by
    simp[Machine.invariant] -- it feels weird that it simplifies so easily, but the invariant
    -- is easy to prove true when the transfer is none, and after this function, it is the case !
}


def Bank.transferExecFalse : OrdinaryEvent (Bank ctx) Unit Unit :=
newEvent''
{
  guard m := m.bankState = Bank_State.Trans ∧
    match m.transfer with
    | none => False
    | some t => ¬ t.transferOK
  action m hgrd :={balance := m.balance, bankState := Op, transfer := none}
  safety m :=
    by
      simp[Machine.invariant]
}


def Bank.Check_balance : OrdinaryEvent (Bank ctx) String Nat :=
newEvent
{
  guard m x := m.bankState = Op ∧ IsElem x m.balance
  action m x hgrd := (Lean.AssocList.search x m.balance hgrd.right,m)
  safety m x :=
    by
      simp
      intros
      assumption
}
