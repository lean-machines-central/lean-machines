
import Mathlib.Data.Finset.Basic

inductive Qualifitication :=
| Elec | Mech | Bio | Chem
  deriving Repr, DecidableEq

structure Alarm where
  text : String
  quali : Qualification
  deriving DecidableEq

abbrev ExpertId := Nat

structure Expert where
  eid : ExpertId
  quali : Qualification
  deriving DecidableEq

structure Period where
  id : Nat
  deriving DecidableEq

abbrev Schedule := List (Period × List ExpertId)

structure Plant where
  experts : List Expert
  schedule : Schedule
  alarms : List Alarm
deriving DecidableEq

def expertOnDuty_aux (exp : Expert) (sched : Schedule) : List Period :=
    match sched with
    |  [] => []
    |  (per, exps)::xs => if exp.eid ∈ exps
                          then per :: expertOnDuty_aux exp xs
                          else expertOnDuty_aux exp xs

def expertOnDuty (exp : Expert) (plant : Plant) : List Period :=
  expertOnDuty_aux exp plant.schedule

def fetchExperts_aux (per : Period) (sched : List (Period × List ExpertId)) :=
  match sched with
  | [] => []
  | (per', exps) :: xs => if per' = per then exps
                          else fetchExperts_aux per xs

def fetchExperts (per : Period) (plant : Plant) : List ExpertId :=
  fetchExperts_aux per plant.schedule

def numberOfExperts (per : Period) (plant : Plant) : Nat :=
  (fetchExperts per plant).length
