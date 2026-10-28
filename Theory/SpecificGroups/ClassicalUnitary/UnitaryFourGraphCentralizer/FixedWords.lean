module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourOuter
public import Mathlib.GroupTheory.Solvable

/-!
# Fixed binary words in the unitary graph centralizer

Four matrices with entries zero and one are fixed by the Hermitian field
involution. Three lie in the point parabolic. A double commutator of these
lies in the flag overlap, but its commutator with the fourth matrix, in the
plane parabolic, has order three. Both word evaluations take place inside
individual endpoints, so they remain valid in every faithful completion
of the marked amalgam.

This supplies the local obstruction in Aschbacher--Smith F.4.36, printed
p.292: a group containing these compatible fixed endpoint images cannot
have a two-group second derived subgroup.
-/
@[expose] public noncomputable section
open Matrix BenderSuzuki.MatrixGroups
open scoped commutatorElement
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourGraphCentralizer
open UnitaryFourFlag
variable (F : Type*) [Field F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "J" => form F σ hσ

def atomMatrix : Fin 4 → Matrix (Fin 4) (Fin 4) F
  | 0 => !![1,0,0,0; 0,1,0,0; 0,1,1,0; 0,0,0,1]
  | 1 => !![1,0,0,0; 0,1,1,0; 0,0,1,0; 0,0,0,1]
  | 2 => !![1,1,0,0; 0,1,0,0; 0,0,1,1; 0,0,0,1]
  | 3 => !![1,0,0,0; 1,1,0,0; 0,0,1,0; 0,0,1,1]

omit [CharP F 2] in
theorem atom_det (k : Fin 4) : (atomMatrix F k).det = 1 := by
  fin_cases k <;>
    simp [atomMatrix, det_succ_column_zero, Fin.sum_univ_succ]

theorem atom_unitary (k : Fin 4) :
    (J).conjTranspose (atomMatrix F k) * gram F * atomMatrix F k = gram F := by
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [atomMatrix, form, gram, HermitianForm.conjTranspose,
      Matrix.mul_apply, Fin.sum_univ_succ, CharTwo.add_self_eq_zero]

/-- The literal binary matrices, in the original unitary coordinates. -/
def atom (k : Fin 4) : SU F J :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (atomMatrix F k)
    (by rw [atom_det]; exact one_ne_zero),
    atom_unitary F σ hσ k, Units.ext (atom_det F k)⟩

@[simp] theorem atom_val (k : Fin 4) : (atom F σ hσ k).val.val = atomMatrix F k := rfl

theorem atom_inv (k : Fin 4) : (atom F σ hσ k)⁻¹ = atom F σ hσ k := by
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  apply Units.ext
  change atomMatrix F k * atomMatrix F k = 1
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [atomMatrix, Matrix.mul_apply, Fin.sum_univ_succ, CharTwo.add_self_eq_zero]

/-- All four actors centralize the specified graph automorphism. -/
theorem atom_fixed (k : Fin 4) :
    UnitaryFourOuter.matrixAut F σ hσ (atom F σ hσ k) = atom F σ hσ k := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  change σ (atomMatrix F k i j) = atomMatrix F k i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;> simp [atomMatrix]

theorem atom_point [Finite F] (k : Fin 3) :
    atom F σ hσ k.castSucc ∈ pointParabolicSU F J := by
  rw [mem_pointParabolicSU]
  fin_cases k <;> simp [atomMatrix]

theorem atom_plane [Finite F] : atom F σ hσ 3 ∈ planeParabolicSU F J := by
  rw [mem_planeParabolicSU]
  simp [atomMatrix]

def firstWord : SU F J := ⁅atom F σ hσ 0, atom F σ hσ 1⁆
def secondWord : SU F J := ⁅atom F σ hσ 1, atom F σ hσ 2⁆
def overlapWord : SU F J := ⁅firstWord F σ hσ, secondWord F σ hσ⁆

private theorem firstWord_val : (firstWord F σ hσ).val.val =
    !![1,0,0,0; 0,0,1,0; 0,1,1,0; 0,0,0,1] := by
  simp only [firstWord, commutatorElement_def, atom_inv]
  change atomMatrix F 0 * atomMatrix F 1 * atomMatrix F 0 * atomMatrix F 1 = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [atomMatrix, Matrix.mul_apply, Fin.sum_univ_succ, CharTwo.add_self_eq_zero]

private theorem firstWord_inv_val : ((firstWord F σ hσ)⁻¹).val.val =
    !![1,0,0,0; 0,1,1,0; 0,1,0,0; 0,0,0,1] := by
  simp only [firstWord, commutatorElement_def, _root_.mul_inv_rev, atom_inv]
  change atomMatrix F 1 * (atomMatrix F 0 * (atomMatrix F 1 * atomMatrix F 0)) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [atomMatrix, Matrix.mul_apply, Fin.sum_univ_succ, CharTwo.add_self_eq_zero]

private theorem secondWord_val : (secondWord F σ hσ).val.val =
    !![1,0,1,1; 0,1,0,1; 0,0,1,0; 0,0,0,1] := by
  simp only [secondWord, commutatorElement_def, atom_inv]
  change atomMatrix F 1 * atomMatrix F 2 * atomMatrix F 1 * atomMatrix F 2 = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [atomMatrix, Matrix.mul_apply, Fin.sum_univ_succ, CharTwo.add_self_eq_zero]

private theorem secondWord_inv_val : ((secondWord F σ hσ)⁻¹).val.val =
    !![1,0,1,1; 0,1,0,1; 0,0,1,0; 0,0,0,1] := by
  simp only [secondWord, commutatorElement_def, _root_.mul_inv_rev, atom_inv]
  change atomMatrix F 2 * (atomMatrix F 1 * (atomMatrix F 2 * atomMatrix F 1)) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [atomMatrix, Matrix.mul_apply, Fin.sum_univ_succ, CharTwo.add_self_eq_zero]

/-- The double commutator is in the original common flag stabilizer. -/
theorem overlapWord_val : (overlapWord F σ hσ).val.val =
    !![1,1,1,1; 0,1,0,1; 0,0,1,1; 0,0,0,1] := by
  change ((firstWord F σ hσ).val.val * (secondWord F σ hσ).val.val *
    ((firstWord F σ hσ)⁻¹).val.val * ((secondWord F σ hσ)⁻¹).val.val) = _
  rw [firstWord_val, secondWord_val, firstWord_inv_val, secondWord_inv_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, CharTwo.add_self_eq_zero]

theorem overlapWord_mem [Finite F] : overlapWord F σ hσ ∈ borelSU F J := by
  constructor
  · change overlapWord F σ hσ ∈ pointParabolicSU F J
    rw [mem_pointParabolicSU]
    simp [overlapWord_val]
  · change overlapWord F σ hσ ∈ planeParabolicSU F J
    rw [mem_planeParabolicSU]
    simp [overlapWord_val]

private theorem overlapWord_inv : (overlapWord F σ hσ)⁻¹ = overlapWord F σ hσ := by
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  apply Units.ext
  change (overlapWord F σ hσ).val.val * (overlapWord F σ hσ).val.val = 1
  rw [overlapWord_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, CharTwo.add_self_eq_zero]

def cubicWord : SU F J := ⁅overlapWord F σ hσ, atom F σ hσ 3⁆

private theorem cubicWord_val : (cubicWord F σ hσ).val.val =
    !![1,1,0,0; 1,0,0,0; 0,0,1,1; 0,0,1,0] := by
  simp only [cubicWord, commutatorElement_def, overlapWord_inv, atom_inv]
  change (overlapWord F σ hσ).val.val * atomMatrix F 3 *
    (overlapWord F σ hσ).val.val * atomMatrix F 3 = _
  rw [overlapWord_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [atomMatrix, Matrix.mul_apply, Fin.sum_univ_succ, CharTwo.add_self_eq_zero]

theorem cubicWord_cube : cubicWord F σ hσ ^ 3 = 1 := by
  apply Subtype.ext
  apply Units.ext
  change ((cubicWord F σ hσ).val.val) ^ 3 = 1
  rw [cubicWord_val]
  simp only [pow_succ, pow_zero, one_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, CharTwo.add_self_eq_zero]

theorem cubicWord_ne_one : cubicWord F σ hσ ≠ 1 := by
  intro h
  have he := congrArg (fun g : SU F J => g.val.val 0 1) h
  rw [cubicWord_val] at he
  exact one_ne_zero he

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourGraphCentralizer
