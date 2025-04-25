import Mathlib.Tactic

import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary
import LeanMachines.Examples.Multiref.Press.Weak_reaction
import LeanMachines.Refinement.Relational.Basic
import LeanMachines.Refinement.Relational.Ordinary
import LeanMachines.Examples.Multiref.Press.Strong_reaction


inductive Status where
  | stopped : Status
  | working : Status
def Status.toBool (s : Status) :=
  match s with
  | stopped => false
  | working => true
@[simp]
def Status.ofBool (s : Bool) :=
  match s with
  | true => working
  | false => stopped

inductive CtrlMod where
  | Motor_On
  | Motor_Off
  | Motor_Act
  | Motor_Desac
