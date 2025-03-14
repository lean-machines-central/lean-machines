-- This module serves as the root of the `EventSystems` library.
-- Import modules here that should be built as part of the library.

-- Abstract machines
import «LeanMachines».Event.Basic
import «LeanMachines».Event.Ordinary
import «LeanMachines».Event.Convergent


-- Algebraic properties of events
import «LeanMachines».Event.Algebra.Basic
import «LeanMachines».Event.Algebra.Ordinary
import «LeanMachines».Event.Algebra.Convergent


-- import «LeanMachines».NonDet.Convergent

-- Relational refinement
import «LeanMachines».Refinement.Relational.Basic
-- import «LeanMachines».Refinement.Relational.Concrete
-- import «LeanMachines».Refinement.Relational.NonDet.Abstract
-- import «LeanMachines».Refinement.Relational.NonDet.Concrete
-- import «LeanMachines».Refinement.Relational.NonDet.Det.Convergent

-- Functional refinement
-- import «LeanMachines».Refinement.Functional.Abstract
-- import «LeanMachines».Refinement.Functional.Concrete
-- import «LeanMachines».Refinement.Functional.NonDet.Abstract
-- import «LeanMachines».Refinement.Functional.NonDet.Concrete
-- import «LeanMachines».Refinement.Functional.NonDet.Det.Convergent

-- Strong (superposition) refinement
-- import «LeanMachines».Refinement.Strong.Abstract
-- import «LeanMachines».Refinement.Strong.Concrete
-- import «LeanMachines».Refinement.Strong.NonDet.Abstract
-- import «LeanMachines».Refinement.Strong.NonDet.Concrete
-- import «LeanMachines».Refinement.Strong.NonDet.Det.Convergent

-- Examples
import «LeanMachines».Examples.Multiref.Tank.Counter0
import «LeanMachines».Examples.Multiref.Tank.Xor0
import «LeanMachines».Examples.Multiref.Tank.Tank


-- Versioning

def LeanMachines.VERSION_MAJ : Nat := 0
def LeanMachines.VERSION_MIN  : Nat := 2
def LeanMachines.VERSION_REV  : Nat := 0

def LeanMachines.VERSION_STS : String := "beta"
