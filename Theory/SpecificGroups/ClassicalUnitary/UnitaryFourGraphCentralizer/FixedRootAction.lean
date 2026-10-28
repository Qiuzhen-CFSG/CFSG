module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourGraphCentralizer.FixedWords
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourShortRoot.RadicalFixed
/-!
# The binary cubic moves the long root

The existing order-three word in the graph-fixed plane endpoint does not
centralize the marked long-root matrix. The single (0,2) entry distinguishes
the two products. This supplies the nontrivial residual action in the PSL₃(2)
exclusion of Aschbacher–Smith F.5.5, printed p.302.
-/
public section
open Matrix BenderSuzuki.MatrixGroups
open scoped commutatorElement
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneRadical UnitaryFourShortRoot
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourGraphCentralizer
variable (F : Type*) [Field F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "J" => form F σ hσ
private theorem overlap_inv : (overlapWord F σ hσ)⁻¹ = overlapWord F σ hσ := by
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  apply Units.ext
  change (overlapWord F σ hσ).val.val * (overlapWord F σ hσ).val.val = 1
  rw [overlapWord_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, CharTwo.add_self_eq_zero]
theorem cubicWord_matrix : (cubicWord F σ hσ).val.val =
    !![1,1,0,0; 1,0,0,0; 0,0,1,1; 0,0,1,0] := by
  simp only [cubicWord, commutatorElement_def, overlap_inv, atom_inv]
  change (overlapWord F σ hσ).val.val * atomMatrix F 3 *
    (overlapWord F σ hσ).val.val * atomMatrix F 3 = _
  rw [overlapWord_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [atomMatrix, Matrix.mul_apply, Fin.sum_univ_succ, CharTwo.add_self_eq_zero]
theorem cubicWord_fixed :
    UnitaryFourOuter.matrixAut F σ hσ (cubicWord F σ hσ) = cubicWord F σ hσ := by
  simp only [cubicWord, overlapWord, firstWord, secondWord,
    map_commutatorElement, atom_fixed]
theorem cubicWord_plane [Finite F] : cubicWord F σ hσ ∈ planeParabolicSU F J := by
  rw [mem_planeParabolicSU]
  simp [cubicWord_matrix]
theorem longRoot_cubicWord_not_commute :
    ¬ Commute (unipotentSU F σ hσ (longParameter F σ)) (cubicWord F σ hσ) := by
  intro hc
  have he := congrArg (fun g : SU F J => g.val.val 0 2) hc.eq
  change ((unipotentSU F σ hσ (longParameter F σ)).val.val *
    (cubicWord F σ hσ).val.val) 0 2 =
    ((cubicWord F σ hσ).val.val *
    (unipotentSU F σ hσ (longParameter F σ)).val.val) 0 2 at he
  rw [cubicWord_matrix] at he
  simp [unipotentSU, unipotentMatrix, longParameter, Matrix.mul_apply, Fin.sum_univ_succ] at he
end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourGraphCentralizer
