/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
The determinant-action generator formulas are adapted from
Atlas/LinearGroups/Orthogonal/D2MatrixImage.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917, via CFSG's
Theory/Representation/OrthogonalFourPlusMatrix/Comparison/Image.lean.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Changes: use the existing split root commutators and transpose isometry to
place both marked factors in the full isometry group's commutator subgroup.
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.FourSpace
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks.MinusEmbedding
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The marked four-space factors lie in the orthogonal commutator group

Right transvections are the displayed hyperbolic roots, which are commutators
with full orthogonal diagonal elements when the field has more than two
members. Transposition of determinant coordinates exchanges the two factors.
Elementary generation of SL₂ therefore places both entire factors in the
commutator subgroup, including over F₃. No perfectness assertion is used.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, A.2.17,
printed p.39, and the orthogonal conventions of GLS3 §2.7.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Matrix Theory.AlgebraicGroup
namespace ClassicalOrthogonal.Fundamental.MinusCentralizer
open FourPlusMatrix TheoremDRootNormalizer.HigherRanks
variable {F : Type*} [Field F]

private theorem right_upper_root (a : F) :
    toOrthogonal (1, SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) a) =
      root (by decide : (1 : Fin 2) ≠ 0) (-a) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  rcases i with i | i <;> fin_cases i
  all_goals
    simp [root_apply_left, root_apply_right,
      toOrthogonal, onD, coordinates, matrixAction,
      SpecialLinearGroup.transvection_coe, Matrix.adjugate_fin_two]
    <;> ring

private theorem right_lower_root (a : F) :
    toOrthogonal (1, SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) a) =
      root (by decide : (0 : Fin 2) ≠ 1) (-a) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  rcases i with i | i <;> fin_cases i
  all_goals
    simp [root_apply_left, root_apply_right,
      toOrthogonal, onD, coordinates, matrixAction,
      SpecialLinearGroup.transvection_coe, Matrix.adjugate_fin_two]
    <;> ring

theorem fourRight_mem_commutator [Finite F] (hq : 2 < Nat.card F)
    (B : SpecialLinearGroup (Fin 2) F) :
    toOrthogonal (1, B) ∈ commutator (O 2 F) := by
  apply Atlas.sl_elementary_induction
    (fun B => toOrthogonal (1, B) ∈ commutator (O 2 F))
  · intro i j hij a
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · rw [right_upper_root]
      exact root_mem_commutator hq _ _
    · rw [right_lower_root]
      exact root_mem_commutator hq _ _
    · exact False.elim (hij rfl)
  · intro A B hA hB
    have he : ((1, A * B) : PairSL (F := F)) = (1, A) * (1, B) := by simp
    rw [he, map_mul]
    exact Subgroup.mul_mem _ hA hB

private def transposeIsometry : O 2 F :=
  ⟨coordinates.trans ((Matrix.transposeLinearEquiv (Fin 2) (Fin 2) F F).trans
    coordinates.symm), (mem_quadraticIsometrySubgroup _ _).mpr (by
      intro x
      rw [← coordinates_det, ← coordinates_det]
      change (coordinates (coordinates.symm (coordinates x).transpose)).det = _
      rw [LinearEquiv.apply_symm_apply, Matrix.det_transpose])⟩

private theorem transpose_right (A : SpecialLinearGroup (Fin 2) F) :
    transposeIsometry * toOrthogonal (1, A.transpose⁻¹) * transposeIsometry⁻¹ =
      toOrthogonal (A, 1) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply coordinates.injective
  change coordinates (coordinates.symm
      (coordinates (coordinates.symm ((1 : SpecialLinearGroup (Fin 2) F).val *
        coordinates (coordinates.symm (coordinates x).transpose) *
        (A.transpose⁻¹)⁻¹.val))).transpose) = _
  simp only [LinearEquiv.apply_symm_apply, inv_inv,
    toOrthogonal_coordinates, inv_one,
    SpecialLinearGroup.transpose, Matrix.transpose_mul, Matrix.transpose_transpose]
  change A.val * (coordinates x * (1 : Mat (F := F)).transpose) = A.val * coordinates x * 1
  simp

theorem fourLeft_mem_commutator [Finite F] (hq : 2 < Nat.card F)
    (A : SpecialLinearGroup (Fin 2) F) :
    toOrthogonal (A, 1) ∈ commutator (O 2 F) := by
  rw [← transpose_right]
  exact Subgroup.Normal.conj_mem inferInstance _ (fourRight_mem_commutator hq _) _

theorem fourMap_mem_commutator [Finite F] (hq : 2 < Nat.card F)
    (g : PairSL (F := F)) : toOrthogonal g ∈ commutator (O 2 F) := by
  have he : g = (g.1, 1) * (1, g.2) := by simp
  rw [he, map_mul]
  exact Subgroup.mul_mem _ (fourLeft_mem_commutator hq _) (fourRight_mem_commutator hq _)

end ClassicalOrthogonal.Fundamental.MinusCentralizer
