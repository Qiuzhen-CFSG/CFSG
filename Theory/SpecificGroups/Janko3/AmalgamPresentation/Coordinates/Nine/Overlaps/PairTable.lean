module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Nine.Overlaps.FiniteTables
import Mathlib.Tactic.FinCases

/-! Checked normalized matrices and generator transitions for the literal projective overlap. -/
@[expose] public section
namespace Sporadic.Janko3.AmalgamPresentation.NineCoordinates.OverlapTables.Pair
open Subgroup

def rowMatrix : Fin 20 → Matrix (Fin 2) (Fin 2) F
  | 0 => !![(⟨1,0⟩:F),(⟨0,0⟩:F);(⟨0,0⟩:F),(⟨1,0⟩:F)]
  | 1 => !![(⟨1,0⟩:F),(⟨1,0⟩:F);(⟨0,0⟩:F),(⟨2,0⟩:F)]
  | 2 => !![(⟨1,0⟩:F),(⟨2,2⟩:F);(⟨2,0⟩:F),(⟨2,0⟩:F)]
  | 3 => !![(⟨0,0⟩:F),(⟨1,0⟩:F);(⟨2,2⟩:F),(⟨2,2⟩:F)]
  | 4 => !![(⟨1,0⟩:F),(⟨2,1⟩:F);(⟨2,0⟩:F),(⟨0,0⟩:F)]
  | 5 => !![(⟨0,0⟩:F),(⟨1,0⟩:F);(⟨1,1⟩:F),(⟨0,0⟩:F)]
  | 6 => !![(⟨1,0⟩:F),(⟨1,1⟩:F);(⟨2,1⟩:F),(⟨2,0⟩:F)]
  | 7 => !![(⟨1,0⟩:F),(⟨1,0⟩:F);(⟨2,2⟩:F),(⟨0,2⟩:F)]
  | 8 => !![(⟨1,0⟩:F),(⟨0,2⟩:F);(⟨2,1⟩:F),(⟨0,1⟩:F)]
  | 9 => !![(⟨1,0⟩:F),(⟨0,0⟩:F);(⟨2,2⟩:F),(⟨2,0⟩:F)]
  | 10 => !![(⟨1,0⟩:F),(⟨1,2⟩:F);(⟨1,2⟩:F),(⟨2,0⟩:F)]
  | 11 => !![(⟨1,0⟩:F),(⟨2,2⟩:F);(⟨0,2⟩:F),(⟨1,2⟩:F)]
  | 12 => !![(⟨1,0⟩:F),(⟨0,1⟩:F);(⟨1,2⟩:F),(⟨2,2⟩:F)]
  | 13 => !![(⟨1,0⟩:F),(⟨2,1⟩:F);(⟨0,2⟩:F),(⟨2,0⟩:F)]
  | 14 => !![(⟨1,0⟩:F),(⟨2,0⟩:F);(⟨1,1⟩:F),(⟨2,0⟩:F)]
  | 15 => !![(⟨1,0⟩:F),(⟨1,1⟩:F);(⟨0,1⟩:F),(⟨1,1⟩:F)]
  | 16 => !![(⟨1,0⟩:F),(⟨2,0⟩:F);(⟨1,1⟩:F),(⟨2,1⟩:F)]
  | 17 => !![(⟨1,0⟩:F),(⟨0,2⟩:F);(⟨0,1⟩:F),(⟨2,0⟩:F)]
  | 18 => !![(⟨1,0⟩:F),(⟨0,1⟩:F);(⟨1,0⟩:F),(⟨2,0⟩:F)]
  | _ => !![(⟨1,0⟩:F),(⟨1,2⟩:F);(⟨1,0⟩:F),(⟨2,0⟩:F)]

theorem rowMatrix_det (i : Fin 20) : (rowMatrix i).det ≠ 0 := by
  have h : ∀ i, (rowMatrix i).det ≠ 0 := by decide +kernel
  exact h i

def row (i : Fin 20) : GL9 := Matrix.GeneralLinearGroup.mkOfDetNeZero (rowMatrix i) (rowMatrix_det i)
noncomputable def repr (i : Fin 20) : P := Matrix.ProjGenLinGroup.mk (row i)
noncomputable def generator (b : Bool) : P := Matrix.ProjGenLinGroup.mk (overlapMatrix (if b then 1 else 0))
noncomputable def subgroup : Subgroup P := closure (Set.range generator)

def parent : Fin 20 → Fin 20
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 1
  | 4 => 2
  | 5 => 3
  | 6 => 4
  | 7 => 5
  | 8 => 6
  | 9 => 7
  | 10 => 8
  | 11 => 9
  | 12 => 10
  | 13 => 11
  | 14 => 12
  | 15 => 13
  | 16 => 14
  | 17 => 15
  | 18 => 16
  | _ => 17

def letter : Fin 20 → Bool
  | 0 => false
  | 1 => false
  | 2 => true
  | 3 => true
  | 4 => false
  | 5 => false
  | 6 => true
  | 7 => true
  | 8 => false
  | 9 => false
  | 10 => true
  | 11 => true
  | 12 => false
  | 13 => false
  | 14 => true
  | 15 => true
  | 16 => false
  | 17 => false
  | 18 => true
  | _ => true

def parentScalar : Fin 20 → F
  | 0 => (⟨1,0⟩:F)
  | 1 => (⟨1,0⟩:F)
  | 2 => (⟨1,0⟩:F)
  | 3 => (⟨1,2⟩:F)
  | 4 => (⟨1,0⟩:F)
  | 5 => (⟨2,0⟩:F)
  | 6 => (⟨2,2⟩:F)
  | 7 => (⟨2,0⟩:F)
  | 8 => (⟨1,0⟩:F)
  | 9 => (⟨1,0⟩:F)
  | 10 => (⟨1,1⟩:F)
  | 11 => (⟨1,0⟩:F)
  | 12 => (⟨1,0⟩:F)
  | 13 => (⟨1,0⟩:F)
  | 14 => (⟨1,2⟩:F)
  | 15 => (⟨2,2⟩:F)
  | 16 => (⟨1,0⟩:F)
  | 17 => (⟨1,0⟩:F)
  | 18 => (⟨2,0⟩:F)
  | _ => (⟨1,1⟩:F)

private def parentUnit (i : Fin 20) : Fˣ := Units.mk0 (parentScalar i) (by
  have h : ∀ i, parentScalar i ≠ 0 := by decide +kernel
  exact h i)

private theorem parent_lt : ∀ i : Fin 20, i ≠ 0 → (parent i).val < i.val := by decide +kernel
private theorem parent_matrix (i : Fin 20) : i ≠ 0 →
    row (parent i) * overlapMatrix (if letter i then 1 else 0) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (parentUnit i) * row i := by
  intro hi
  apply Matrix.GeneralLinearGroup.ext
  intro j k
  fin_cases j <;> fin_cases k <;> revert i <;> decide +kernel

private theorem repr_zero : repr 0 = 1 := by
  change Matrix.ProjGenLinGroup.mk (row 0) = 1
  rw [show row 0 = 1 from by apply Matrix.GeneralLinearGroup.ext; intro j k; fin_cases j <;> fin_cases k <;> decide +kernel,map_one]

private theorem parent_repr (i : Fin 20) (hi : i ≠ 0) :
    repr i = repr (parent i) * generator (letter i) := by
  change _ = Matrix.ProjGenLinGroup.mk _ * Matrix.ProjGenLinGroup.mk _
  rw [←map_mul,parent_matrix i hi,map_mul,Matrix.ProjGenLinGroup.mk_scalar,one_mul]
  rfl

def next : Fin 20 → Fin 4 → Fin 20
  | 0 => ![1,1,2,2]
  | 1 => ![0,0,3,3]
  | 2 => ![4,4,0,0]
  | 3 => ![5,5,1,1]
  | 4 => ![2,2,6,6]
  | 5 => ![3,3,7,7]
  | 6 => ![8,8,4,4]
  | 7 => ![9,9,5,5]
  | 8 => ![6,6,10,10]
  | 9 => ![7,7,11,11]
  | 10 => ![12,12,8,8]
  | 11 => ![13,13,9,9]
  | 12 => ![10,10,14,14]
  | 13 => ![11,11,15,15]
  | 14 => ![16,16,12,12]
  | 15 => ![17,17,13,13]
  | 16 => ![14,14,18,18]
  | 17 => ![15,15,19,19]
  | 18 => ![19,19,16,16]
  | _ => ![18,18,17,17]

def stepScalar : Fin 20 → Fin 4 → F
  | 0 => ![(⟨1,0⟩:F),(⟨1,0⟩:F),(⟨1,0⟩:F),(⟨1,1⟩:F)]
  | 1 => ![(⟨1,0⟩:F),(⟨1,0⟩:F),(⟨1,2⟩:F),(⟨2,0⟩:F)]
  | 2 => ![(⟨1,0⟩:F),(⟨1,0⟩:F),(⟨2,1⟩:F),(⟨1,0⟩:F)]
  | 3 => ![(⟨2,0⟩:F),(⟨2,0⟩:F),(⟨2,0⟩:F),(⟨2,2⟩:F)]
  | 4 => ![(⟨1,0⟩:F),(⟨1,0⟩:F),(⟨2,2⟩:F),(⟨0,1⟩:F)]
  | 5 => ![(⟨2,0⟩:F),(⟨2,0⟩:F),(⟨2,0⟩:F),(⟨2,2⟩:F)]
  | 6 => ![(⟨1,0⟩:F),(⟨1,0⟩:F),(⟨0,2⟩:F),(⟨1,2⟩:F)]
  | 7 => ![(⟨1,0⟩:F),(⟨1,0⟩:F),(⟨1,2⟩:F),(⟨2,0⟩:F)]
  | 8 => ![(⟨1,0⟩:F),(⟨1,0⟩:F),(⟨1,1⟩:F),(⟨0,2⟩:F)]
  | 9 => ![(⟨1,0⟩:F),(⟨1,0⟩:F),(⟨1,0⟩:F),(⟨1,1⟩:F)]
  | 10 => ![(⟨1,0⟩:F),(⟨1,0⟩:F),(⟨0,1⟩:F),(⟨2,1⟩:F)]
  | 11 => ![(⟨1,0⟩:F),(⟨1,0⟩:F),(⟨2,1⟩:F),(⟨1,0⟩:F)]
  | 12 => ![(⟨1,0⟩:F),(⟨1,0⟩:F),(⟨1,2⟩:F),(⟨2,0⟩:F)]
  | 13 => ![(⟨1,0⟩:F),(⟨1,0⟩:F),(⟨2,2⟩:F),(⟨0,1⟩:F)]
  | 14 => ![(⟨1,0⟩:F),(⟨1,0⟩:F),(⟨2,0⟩:F),(⟨2,2⟩:F)]
  | 15 => ![(⟨1,0⟩:F),(⟨1,0⟩:F),(⟨0,2⟩:F),(⟨1,2⟩:F)]
  | 16 => ![(⟨1,0⟩:F),(⟨1,0⟩:F),(⟨2,0⟩:F),(⟨2,2⟩:F)]
  | 17 => ![(⟨1,0⟩:F),(⟨1,0⟩:F),(⟨1,1⟩:F),(⟨0,2⟩:F)]
  | 18 => ![(⟨1,0⟩:F),(⟨1,0⟩:F),(⟨1,2⟩:F),(⟨2,0⟩:F)]
  | _ => ![(⟨1,0⟩:F),(⟨1,0⟩:F),(⟨0,1⟩:F),(⟨2,1⟩:F)]

private def stepUnit (i : Fin 20) (j : Fin 4) : Fˣ := Units.mk0 (stepScalar i j) (by
  have h : ∀ i j, stepScalar i j ≠ 0 := by decide +kernel
  exact h i j)
private def signedMatrix (j : Fin 4) : GL9 :=
  if j.val % 2 = 0 then overlapMatrix (if j.val < 2 then 0 else 1)
  else (overlapMatrix (if j.val < 2 then 0 else 1))⁻¹
private theorem step_matrix (i : Fin 20) (j : Fin 4) :
    row i * signedMatrix j = Matrix.GeneralLinearGroup.scalar (Fin 2) (stepUnit i j) * row (next i j) := by
  apply Matrix.GeneralLinearGroup.ext
  intro k l
  fin_cases k <;> fin_cases l <;> fin_cases j <;> revert i <;> decide +kernel
private theorem step_repr (i : Fin 20) (j : Fin 4) :
    repr i * Matrix.ProjGenLinGroup.mk (signedMatrix j) = repr (next i j) := by
  change Matrix.ProjGenLinGroup.mk _ * Matrix.ProjGenLinGroup.mk _ = Matrix.ProjGenLinGroup.mk _
  rw [←map_mul,step_matrix,map_mul,Matrix.ProjGenLinGroup.mk_scalar,one_mul]

/-- The table is exactly the actual projective word subgroup. -/
theorem carrier_eq : (subgroup : Set P) = Set.range repr := by
  apply closure_eq_range generator repr 0 repr_zero
    (row_mem_of_parent generator repr repr_zero parent letter parent_lt parent_repr)
  · intro i b
    cases b
    · exact ⟨next i 0,step_repr i 0⟩
    · exact ⟨next i 2,step_repr i 2⟩
  · intro i b
    cases b
    · exact ⟨next i 1,by simpa [signedMatrix,generator] using step_repr i 1⟩
    · exact ⟨next i 3,by simpa [signedMatrix,generator] using step_repr i 3⟩

private theorem row_pivot : ∀ i : Fin 20, pivot (row i) = 1 := by decide +kernel
private theorem rowMatrix_injective : Function.Injective rowMatrix := by decide +kernel

theorem repr_injective : Function.Injective repr := by
  intro i j hij
  have he := normalized_injective (row_pivot i) (row_pivot j) hij
  apply rowMatrix_injective
  exact congrArg (fun m : GL9 => (m : Matrix (Fin 2) (Fin 2) F)) he

theorem subgroup_card : Nat.card subgroup = 20 := card_of_range subgroup repr repr_injective carrier_eq

end Sporadic.Janko3.AmalgamPresentation.NineCoordinates.OverlapTables.Pair
