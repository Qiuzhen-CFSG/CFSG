module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.SylowTwoPart.KernelCardinality
public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Tactic
/-!
# Center-detecting coordinates for the literal J₄ max4 two-core

The differences of the fifteen certified word matrices are strictly lower
for a three-block flag. Twelve selected commutator entries detect the first
twelve word coordinates: their binary coefficient matrix has a checked inverse.
All certificates use kernel reduction on the existing literal word matrices.

Source: the ATLAS max4 program and the coordinate basis documented in
`SymmetricLinear.SylowTwoPart.KernelCardinality`.
-/

@[expose] public section
namespace Janko4.LocalStructure.SymmetricLinear.CoreCenter
open Janko4.LocalStructure.SymmetricLinear.SylowTwoPart.KernelCardinality
open scoped BigOperators

def difference (i : Fin 15) : SmallMatrix := decode (pivotRows.get i) - 1

def block (i : Fin 28) : Fin 3 := if i.val < 4 then 0 else if i.val < 16 then 1 else 2

def detector : Fin 12 → Fin 15 :=
  ![0, 0, 0, 1, 1, 1, 2, 2, 2, 3, 3, 4]

def row : Fin 12 → Fin 28 :=
  ![16, 16, 17, 16, 16, 17, 16, 16, 17, 16, 16, 16]

def column : Fin 12 → Fin 28 :=
  ![0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 0]

def coeff : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0],
    ![0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0],
    ![0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0],
    ![0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0],
    ![1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0],
    ![1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1],
    ![0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1],
    ![0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0]]

def inverse : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0],
    ![1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1],
    ![1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1],
    ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1],
    ![1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1],
    ![1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0],
    ![0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0],
    ![0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1]]

set_option maxRecDepth 2000 in
 theorem strict (k : Fin 15) : ∀ i j, block i ≤ block j → difference k i j = 0 := by
  simp only [difference, Matrix.sub_apply]
  revert k
  decide +kernel

 theorem inverse_mul : inverse * coeff = 1 := by decide +kernel

 theorem coefficient (k : Fin 12) (i : Fin 15) :
    (difference i * difference (detector k) - difference (detector k) * difference i)
      (row k) (column k) = if h : i.val < 12 then coeff k ⟨i.val,h⟩ else 0 := by
  revert k i
  decide +kernel
end Janko4.LocalStructure.SymmetricLinear.CoreCenter
