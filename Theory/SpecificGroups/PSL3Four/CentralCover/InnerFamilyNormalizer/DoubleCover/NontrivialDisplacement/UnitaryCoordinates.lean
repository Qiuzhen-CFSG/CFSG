module

public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.DoubleCover.NontrivialDisplacement.SourceData
public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.Centerless
public import Theory.SpecificGroups.PSL3Four.SylowModel.MatrixRealization

/-!
# Graph-field-compatible Sylow coordinates in PSL₃(4)

Permuting the upper-unitriangular basis into order `(0,2,1)` gives the matrix
`[1,c,x; 0,1,0; 0,y,1]`. Relative to the Hermitian Gram matrix exchanging
the first two basis vectors, inverse transpose followed by Frobenius sends
its coordinates to `(y²,x²,c²+(xy)²)`.

The fusion witness from `Centerless.exists_fusion`, proved there using
`Centerless.fusionSL_gram`, transports this action to the standard graph-field
automorphism: conjugate by the inverse of that witness. Faithfulness follows
from `MatrixRealization.projective_injective` and the two conjugations. The
range has order 64, the full two-part of the order of PSL₃(4), so it is Sylow.

This constructs the coordinate input for the center-C₂ graph-field argument;
the separate involution-lifting and covering-group arguments use I.2.2(3b).
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
I.2.2(3b), printed pp.409–410, and 16.4.9(2), printed p.1191.
-/

public section
open Matrix Subgroup
namespace Matrix.PSL3Four.InnerFamilyNormalizer.DoubleCover.NontrivialDisplacement
namespace UnitaryCoordinates
open SylowModel ExtendedCentralizer.ProjectiveFixer ProjectiveGraphField
noncomputable section

private def rotationSL : SL := ⟨!![1,0,0;0,0,1;0,1,0], by
  simp [Matrix.det_fin_three, CharTwo.neg_eq]⟩

private theorem rotationSL_sq : rotationSL * rotationSL = 1 := by
  apply Subtype.ext
  change rotationSL.val * rotationSL.val = (1 : Matrix (Fin 3) (Fin 3) F)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotationSL, Matrix.mul_apply, Fin.sum_univ_three]

private theorem rotationSL_inv : rotationSL⁻¹ = rotationSL :=
  inv_eq_of_mul_eq_one_right rotationSL_sq

private def rotatedSL : U →* SL :=
  (MulAut.conj rotationSL).toMonoidHom.comp MatrixRealization.specialLinear

private theorem rotatedSL_matrix (u : U) :
    (rotatedSL u).val = !![1,u.c,u.x;0,1,0;0,u.y,1] := by
  change (rotationSL * MatrixRealization.specialLinear u * rotationSL⁻¹).val = _
  rw [rotationSL_inv]
  change rotationSL.val * MatrixRealization.matrix u * rotationSL.val = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotationSL, MatrixRealization.matrix, Matrix.mul_apply, Fin.sum_univ_three]

private def flip (u : U) : U := ⟨u.y ^ 2, u.x ^ 2, u.c ^ 2 + (u.x * u.y) ^ 2⟩

private theorem flip_matrix (u : U) :
    slAction (rotatedSL u) = Centerless.vSL * rotatedSL (flip u) * Centerless.vSL := by
  rw [slAction_apply]
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  change (slFrobenius (rotatedSL u)).val.transpose *
    (Centerless.vSL.val * (rotatedSL (flip u)).val * Centerless.vSL.val) =
      (1 : Matrix (Fin 3) (Fin 3) F)
  have hf : (slFrobenius (rotatedSL u)).val =
      (rotatedSL u).val.map (fun x => x ^ 2) := by
    ext r c
    exact slFrobenius_apply _ r c
  rw [hf, rotatedSL_matrix, rotatedSL_matrix]
  have hchar : CharP F 2 := inferInstance
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Centerless.vSL, flip, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.transpose_apply, Matrix.map_apply] <;>
    ring_nf <;> reduce_mod_char!


private def rotated : U →* PSL :=
  (MulAut.conj (project rotationSL)).toMonoidHom.comp MatrixRealization.projective

private theorem rotated_injective : Function.Injective rotated :=
  (MulAut.conj (project rotationSL)).injective.comp MatrixRealization.projective_injective

private theorem rotated_project (u : U) : rotated u = project (rotatedSL u) := by
  change project rotationSL * project (MatrixRealization.specialLinear u) *
    (project rotationSL)⁻¹ = project (rotationSL * MatrixRealization.specialLinear u * rotationSL⁻¹)
  simp only [map_mul, map_inv]

private theorem rotated_flip (u : U) :
    MulAut.conj Centerless.v (graphField (rotated u)) = rotated (flip u) := by
  rw [MulAut.conj_apply, rotated_project, rotated_project]
  change project Centerless.vSL * project (slAction (rotatedSL u)) *
    (project Centerless.vSL)⁻¹ = project (rotatedSL (flip u))
  rw [flip_matrix]
  have hv : Centerless.vSL * Centerless.vSL = 1 := by
    simpa only [pow_two] using Centerless.v_sq
  rw [← map_inv, ← map_mul, ← map_mul]
  apply congrArg project
  simp only [← mul_assoc, hv, one_mul, mul_inv_cancel_right]

private def fusion : PSL := Classical.choose Centerless.exists_fusion

private theorem fusion_eq : fusion * graphField (fusion⁻¹) = Centerless.v :=
  Classical.choose_spec Centerless.exists_fusion

private def embedding : U →* PSL :=
  (MulAut.conj fusion⁻¹).toMonoidHom.comp rotated

private theorem embedding_injective : Function.Injective embedding :=
  (MulAut.conj fusion⁻¹).injective.comp rotated_injective

private theorem compatible (u : U) : graphField (embedding u) = embedding (flip u) := by
  change graphField (MulAut.conj fusion⁻¹ (rotated u)) =
    MulAut.conj fusion⁻¹ (rotated (flip u))
  rw [← rotated_flip]
  change graphField (fusion⁻¹ * rotated u * (fusion⁻¹)⁻¹) =
    fusion⁻¹ * (Centerless.v * graphField (rotated u) * Centerless.v⁻¹) * (fusion⁻¹)⁻¹
  simp only [← fusion_eq, map_mul, map_inv, inv_inv]
  group

private theorem card_range : Nat.card embedding.range = 64 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective embedding_injective).toEquiv, card_U]

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private def sylow : Sylow 2 PSL := Sylow.ofCard embedding.range (by
  rw [card_range, card_PSL]
  decide +kernel)

end
end UnitaryCoordinates

/-- A faithful graph-field-compatible realization of UT₃(F₄) as a Sylow
 two-subgroup of the concrete PSL₃(4). -/
noncomputable def unitarySylowModel : UnitarySylowModel where
  embedding := UnitaryCoordinates.embedding
  injective := UnitaryCoordinates.embedding_injective
  sylow := UnitaryCoordinates.sylow
  range_eq := rfl
  compatible := UnitaryCoordinates.compatible

end Matrix.PSL3Four.InnerFamilyNormalizer.DoubleCover.NontrivialDisplacement
