module
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.LinearNormalizer.CoreRecognition.ProjectiveData
import Mathlib.Algebra.CharP.Two
import Mathlib.Order.Fin.Basic

/-!
# Scalar triples in the core configuration

The quadratic identity J² = 1 + J makes the three nonzero scalar multiples
cyclic. Matrices commuting with J therefore transport scalar triples.
The published packed representatives are their minima, and are strictly
increasing, so the 231 triples are distinct.

The original matrices and attribution are in `../../../LinearModel/source/`;
the candidate representatives are recorded in `../source/projective-certificate.json`.
All finite identities below are checked by the Lean kernel.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
namespace CoreProjectiveAction

abbrev Row := Fin 12 → ZMod 2

private theorem j_square : matrixJ * matrixJ = 1 + matrixJ := by decide +kernel

private theorem row_jj (v : Row) : Matrix.vecMul (Matrix.vecMul v matrixJ) matrixJ =
    v + Matrix.vecMul v matrixJ := by
  rw [Matrix.vecMul_vecMul, j_square, Matrix.vecMul_add, Matrix.vecMul_one]

private theorem row_cancel_left (v w : Row) : v + (v + w) = w := by
  funext i
  exact CharTwo.add_cancel_left _ _

private theorem row_cancel_right (v w : Row) : v + w + w = v := by
  funext i
  exact CharTwo.add_cancel_right _ _

private theorem triple_cycle {α : Type*} (a b c : α) :
    ({b, c, a} : Set α) = {a, b, c} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem triple_cycle₂ {α : Type*} (a b c : α) :
    ({c, a, b} : Set α) = {a, b, c} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem row_cancel_middle (v w : Row) : v + w + v = w := by
  rw [add_comm v w, row_cancel_right]

theorem scalarLine_of_mem {v w : Row} (h : w ∈ scalarLine v) :
    scalarLine w = scalarLine v := by
  have hc : Matrix.vecMul v matrixJ + (v + Matrix.vecMul v matrixJ) = v := by
    rw [add_comm v, row_cancel_left]
  rcases h with rfl | rfl | rfl
  · rfl
  · simp only [scalarLine, row_jj, hc]
    exact triple_cycle _ _ _
  · simp only [scalarLine, Matrix.add_vecMul, row_jj, hc, row_cancel_middle]
    exact triple_cycle₂ _ _ _

theorem scalarLine_image (v : Row) (M : Matrix12) (h : Commute M matrixJ) :
    (fun w => Matrix.vecMul w M) '' scalarLine v = scalarLine (Matrix.vecMul v M) := by
  have hc : Matrix.vecMul (Matrix.vecMul v matrixJ) M =
      Matrix.vecMul (Matrix.vecMul v M) matrixJ := by
    rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, h.eq]
  simp only [scalarLine, Set.image_insert_eq, Set.image_singleton,
    Matrix.add_vecMul, hc]

private def vectorCode (v : Row) : ℕ := ∑ j : Fin 12, (v j).val * 2 ^ j.val

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem minima : ∀ i : Fin 231,
    vectorCode (projectiveVector i) = projectiveRepresentative i ∧
    projectiveRepresentative i ≤ vectorCode (Matrix.vecMul (projectiveVector i) matrixJ) ∧
    projectiveRepresentative i ≤ vectorCode (projectiveVector i + Matrix.vecMul (projectiveVector i) matrixJ) := by
  decide +kernel

private theorem representative_inj : Function.Injective projectiveRepresentative := by
  apply StrictMono.injective
  rw [Fin.strictMono_iff_lt_succ]
  decide +kernel

theorem line_inj : Function.Injective (fun i => scalarLine (projectiveVector i)) := by
  have lower : ∀ i v, v ∈ scalarLine (projectiveVector i) → projectiveRepresentative i ≤ vectorCode v := by
    intro i v hv
    rcases hv with rfl | rfl | rfl
    · exact (minima i).1.ge
    · exact (minima i).2.1
    · exact (minima i).2.2
  intro i j hij
  change scalarLine (projectiveVector i) = scalarLine (projectiveVector j) at hij
  apply representative_inj
  apply le_antisymm
  · rw [← (minima j).1]
    apply lower
    rw [hij]
    exact Or.inl rfl
  · rw [← (minima i).1]
    apply lower
    rw [← hij]
    exact Or.inl rfl

end CoreProjectiveAction
end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
