module

public import Theory.Representation.SL3.BinaryDefiningFactors
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Basic

/-!
# Tensorwise transpose on adjoint words

The adjoint factor is the literal trace kernel of endomorphisms of the natural
three-space. Transpose preserves it and moves at least three dimensions: the
three upper entries of its displacement can be prescribed independently.
Tensoring these operators constructs a square-one operator on any word.
The natural and dual cases are assigned identity solely to make the recursive
operator total; the displacement consumer requires their absence.

Source: Guralnick--Malle, Classification of 2F-modules II, Proposition 4.11,
internal pp.31--32, and the tensor estimates of §2.2 and §3.5.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module
open scoped TensorProduct
open Representation.SL3.BinaryDefiningFactors
open Representation.BinaryOffender.NaturalTensor
namespace Representation.SU3.CubicDegree.SchurOuter.GraphStable.TensorDisplacement
variable {K : Type*} [Field K]

/-- Transpose on the trace-zero carrier, using the actual factor module structures. -/
@[expose] def adjointTranspose : Module.End K (Space K .adjoint) where
  toFun X := ⟨(LinearMap.toMatrix' X.val).transpose.toLin', by
    change LinearMap.trace K (Fin 3 → K) _ = 0
    rw [Matrix.trace_toLin'_eq, Matrix.trace_transpose]
    rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_toMatrix']
    exact X.property⟩
  map_add' X Y := by
    apply Subtype.ext
    change (LinearMap.toMatrix' (X.val + Y.val)).transpose.toLin' =
      (LinearMap.toMatrix' X.val).transpose.toLin' +
        (LinearMap.toMatrix' Y.val).transpose.toLin'
    simp
  map_smul' c X := by
    apply Subtype.ext
    change (LinearMap.toMatrix' (c • X.val)).transpose.toLin' =
      c • (LinearMap.toMatrix' X.val).transpose.toLin'
    simp

/-- The operator is literal transpose in the standard natural coordinates. -/
theorem adjointTranspose_matrix (X : Space K .adjoint) :
    LinearMap.toMatrix' (adjointTranspose X).val = (LinearMap.toMatrix' X.val).transpose := by
  exact LinearMap.toMatrix'_toLin' _

/-- Transpose squares to the identity on the trace kernel. -/
theorem adjointTranspose_sq :
    (adjointTranspose (K := K)) * adjointTranspose = 1 := by
  apply LinearMap.ext
  intro X
  apply Subtype.ext
  apply LinearMap.toMatrix'.injective
  simp only [Module.End.mul_apply, Module.End.one_apply, adjointTranspose_matrix,
    Matrix.transpose_transpose]

private def upperEntries : Space K .adjoint →ₗ[K] (Fin 3 → K) where
  toFun X := ![LinearMap.toMatrix' X.val 0 1, LinearMap.toMatrix' X.val 0 2,
    LinearMap.toMatrix' X.val 1 2]
  map_add' X Y := by ext i; fin_cases i <;> rfl
  map_smul' c X := by ext i; fin_cases i <;> rfl

private theorem upperEntries_displacement_surjective :
    Function.Surjective ((upperEntries (K := K)).comp (adjointTranspose (K := K) - 1 : Module.End K (Space K .adjoint))) := by
  intro v
  let M : Matrix (Fin 3) (Fin 3) K := !![0,0,0;v 0,0,0;v 1,v 2,0]
  let X : Space K .adjoint := ⟨M.toLin', by simp [M, Matrix.trace, Fin.sum_univ_three]⟩
  refine ⟨X, ?_⟩
  change upperEntries (adjointTranspose X - X) = v
  have hx : LinearMap.toMatrix' X.val = M := LinearMap.toMatrix'_toLin' M
  have hm : LinearMap.toMatrix' (adjointTranspose X - X).val = M.transpose - M := by
    change LinearMap.toMatrix' ((adjointTranspose X).val - X.val) = _
    rw [map_sub, adjointTranspose_matrix, hx]
  change ![LinearMap.toMatrix' (adjointTranspose X - X).val 0 1,
    LinearMap.toMatrix' (adjointTranspose X - X).val 0 2,
    LinearMap.toMatrix' (adjointTranspose X - X).val 1 2] = v
  rw [hm]
  ext i
  fin_cases i <;> simp [M]

/-- The three strictly lower entries give independent displacement coordinates. -/
theorem three_le_adjointTranspose_displacement :
    3 ≤ operatorFixedCodim (k := K) (V := Space K .adjoint) (adjointTranspose (K := K)) := by
  let f : LinearMap.range (adjointTranspose (K := K) - 1 : Module.End K (Space K .adjoint)) →ₗ[K] (Fin 3 → K) :=
    upperEntries.comp (LinearMap.range (adjointTranspose (K := K) - 1 : Module.End K (Space K .adjoint))).subtype
  have hf : Function.Surjective f := by
    intro v
    obtain ⟨X,hX⟩ := upperEntries_displacement_surjective (K := K) v
    exact ⟨⟨(adjointTranspose (K := K) - 1 : Module.End K (Space K .adjoint)) X, X, rfl⟩, hX⟩
  simpa only [operatorFixedCodim, Module.finrank_pi, Fintype.card_fin, Module.finrank_self, Nat.mul_one]
    using LinearMap.finrank_le_finrank_of_surjective hf

/-- The canonical adjoint transpose; unused natural labels are assigned identity. -/
@[expose] def factorTranspose : (a : Factor) → Module.End K (Space K a)
  | .trivial => 1
  | .natural => 1
  | .dual => 1
  | .adjoint => adjointTranspose

/-- Tensorwise transpose, retaining every trivial factor and every word position. -/
@[expose] def wordTranspose : (w : List Factor) → Module.End K (WordSpace K w)
  | [] => 1
  | a :: w => TensorProduct.map (factorTranspose a) (wordTranspose w)

/-- Every canonical factor operator squares to one. -/
theorem factorTranspose_sq (a : Factor) :
    (factorTranspose (K := K) a) * factorTranspose a = 1 := by
  cases a with
  | adjoint => exact adjointTranspose_sq
  | trivial | natural | dual => exact one_mul 1

/-- The canonical operator on a word squares to one. -/
theorem wordTranspose_sq (w : List Factor) :
    (wordTranspose (K := K) w) * wordTranspose w = 1 := by
  induction w with
  | nil => exact one_mul 1
  | cons a w ih =>
    change TensorProduct.map _ _ * TensorProduct.map _ _ = 1
    rw [← TensorProduct.map_mul, factorTranspose_sq, ih, TensorProduct.map_one]

end Representation.SU3.CubicDegree.SchurOuter.GraphStable.TensorDisplacement
