

import «LeanMachines»

def main : IO Unit :=
  IO.println s!"Lean Machines v.{LeanMachines.VERSION_MAJ}.{LeanMachines.VERSION_MIN}.{LeanMachines.VERSION_REV} {LeanMachines.VERSION_STS}"
