module

public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.FixedStructure.CentralKernel
public import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Tactic.FinCases

/-!
# The actual twenty-one point cover for the Held outer fixed subgroup

The orbit of letter `30` is identified with the two-subsets of seven letters.
The two generator actions then identify the actual orbit image with `A₇`.
The finite action certificate is kept here, below the central-kernel interface.
All permutation computations use the checked fast Bray table.

Source: GLS3 Table 5.3p, outer 2C row, and the ATLAS pair correspondence
recorded in `FixedStructure/Source/README.md`.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace Held.OuterInvolution.FixedStructure

set_option Elab.async false
set_option maxRecDepth 4096

abbrev Pair7 := ↥(Set.powersetCard (Fin 7) 2)

def orbitPoints : Fin 21 → Fin 2058 :=
  ![30, 65, 129, 288, 389, 392, 411, 690, 946, 1167, 1191,
    1424, 1469, 1480, 1561, 1638, 1671, 1767, 2033, 2036, 2042]

def pairPointsVal : Fin 21 → Finset (Fin 7) :=
  ![{4, 6}, {0, 5}, {0, 2}, {4, 5}, {3, 6}, {3, 5}, {3, 4}, {0, 6},
    {1, 6}, {2, 3}, {2, 4}, {1, 2}, {0, 1}, {1, 5}, {0, 4}, {1, 3},
    {2, 5}, {2, 6}, {1, 4}, {0, 3}, {5, 6}]

def pairPoints : Fin 21 → Pair7 := fun i =>
  ⟨pairPointsVal i, by
    change (pairPointsVal i).card = 2
    fin_cases i <;> decide⟩

theorem orbitPoints_injective : Function.Injective orbitPoints := by
  decide +kernel

theorem pairPoints_injective : Function.Injective pairPoints := by
  intro i j h
  have hv := congrArg (fun p : Pair7 => (p : Finset (Fin 7))) h
  exact (by decide +kernel : Function.Injective pairPointsVal) hv

def xPerm : Equiv.Perm (Fin 7) :=
  Equiv.swap 0 5 * Equiv.swap 5 2 * Equiv.swap 2 6 * Equiv.swap 6 1

def yPerm : Equiv.Perm (Fin 7) :=
  Equiv.swap 0 1 * Equiv.swap 1 6 * Equiv.swap 6 4 * Equiv.swap 4 2 *
    Equiv.swap 2 5 * Equiv.swap 5 3

theorem xPerm_even : xPerm ∈ alternatingGroup (Fin 7) := by
  change Equiv.Perm.sign xPerm = 1
  decide
theorem yPerm_even : yPerm ∈ alternatingGroup (Fin 7) := by
  change Equiv.Perm.sign yPerm = 1
  decide

def xAlt : alternatingGroup (Fin 7) := ⟨xPerm, xPerm_even⟩
def yAlt : alternatingGroup (Fin 7) := ⟨yPerm, yPerm_even⟩

theorem orbitPoints_x : ∀ i : Fin 21,
    representation (first : fixed).val (orbitPoints i) = orbitPoints (![18,16,20,10,15,9,6,13,12,4,0,7,1,2,3,19,17,8,14,5,11] i) := by
  intro i
  change representation (bray ^ 2) _ = _
  rw [map_pow, bray_representation]
  fin_cases i <;> decide +kernel

theorem orbitPoints_y : ∀ i : Fin 21,
    representation (second : fixed).val (orbitPoints i) = orbitPoints (![10,15,13,9,14,19,2,18,0,1,16,20,8,4,11,7,5,3,17,12,6] i) := by
  intro i
  change representation ((a * bray) ^ 12) _ = _
  rw [map_pow, map_mul, bray_representation]
  fin_cases i <;> decide +kernel

theorem pairPoints_x : ∀ i : Fin 21, xAlt • pairPoints i =
    pairPoints (![18,16,20,10,15,9,6,13,12,4,0,7,1,2,3,19,17,8,14,5,11] i) := by
  intro i
  fin_cases i <;> decide

theorem pairPoints_y : ∀ i : Fin 21, yAlt • pairPoints i =
    pairPoints (![10,15,13,9,14,19,2,18,0,1,16,20,8,4,11,7,5,3,17,12,6] i) := by
  intro i
  fin_cases i <;> decide

def pointPermX : Equiv.Perm (Fin 21) :=
  Equiv.ofBijective ![18,16,20,10,15,9,6,13,12,4,0,7,1,2,3,19,17,8,14,5,11] (by decide)

def pointPermY : Equiv.Perm (Fin 21) :=
  Equiv.ofBijective ![10,15,13,9,14,19,2,18,0,1,16,20,8,4,11,7,5,3,17,12,6] (by decide)

theorem firstGenerator_smul_orbitPoints (i : Fin 21) :
    firstGenerator • (orbitPoints i) = orbitPoints (pointPermX i) := by
  change representation (first : fixed).val (orbitPoints i) = _
  exact orbitPoints_x i

theorem secondGenerator_smul_orbitPoints (i : Fin 21) :
    secondGenerator • (orbitPoints i) = orbitPoints (pointPermY i) := by
  change representation (second : fixed).val (orbitPoints i) = _
  exact orbitPoints_y i

theorem firstGenerator_inv_smul_orbitPoints (i : Fin 21) :
    firstGenerator⁻¹ • (orbitPoints i) = orbitPoints (pointPermX.symm i) := by
  have h := firstGenerator_smul_orbitPoints (pointPermX.symm i)
  have h' : firstGenerator • orbitPoints (pointPermX.symm i) = orbitPoints i := by simpa using h
  rw [← h', ← mul_smul]
  simp

theorem secondGenerator_inv_smul_orbitPoints (i : Fin 21) :
    secondGenerator⁻¹ • (orbitPoints i) = orbitPoints (pointPermY.symm i) := by
  have h := secondGenerator_smul_orbitPoints (pointPermY.symm i)
  have h' : secondGenerator • orbitPoints (pointPermY.symm i) = orbitPoints i := by simpa using h
  rw [← h', ← mul_smul]
  simp

end Held.OuterInvolution.FixedStructure
