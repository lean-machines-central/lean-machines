-- This module serves as the root of the `EventSystems` library.
-- Import modules here that should be built as part of the library.

-- Abstract machines
import «LeanMachines».Event.Convergent
import «LeanMachines».NonDet.Convergent

-- Relational refinement
import «LeanMachines».Refinement.Relational.Abstract
import «LeanMachines».Refinement.Relational.Concrete
import «LeanMachines».Refinement.Relational.NonDet.Abstract
import «LeanMachines».Refinement.Relational.NonDet.Concrete
import «LeanMachines».Refinement.Relational.NonDet.Det.Convergent

-- Functional refinement
import «LeanMachines».Refinement.Functional.Abstract
import «LeanMachines».Refinement.Functional.Concrete
import «LeanMachines».Refinement.Functional.NonDet.Abstract
import «LeanMachines».Refinement.Functional.NonDet.Concrete
import «LeanMachines».Refinement.Functional.NonDet.Det.Convergent

-- Strong (superposition) refinement
import «LeanMachines».Refinement.Strong.Abstract
import «LeanMachines».Refinement.Strong.Concrete
import «LeanMachines».Refinement.Strong.NonDet.Abstract
import «LeanMachines».Refinement.Strong.NonDet.Concrete
import «LeanMachines».Refinement.Strong.NonDet.Det.Convergent

-- Versioning

def LeanMachines.VERSION_MAJ : Nat := 0
def LeanMachines.VERSION_MIN  : Nat := 2
def LeanMachines.VERSION_REV  : Nat := 0

def LeanMachines.VERSION_STS : String := "beta"
