module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCenterReduction
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalForm.Product00
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalForm.Product01
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalForm.Product02
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalForm.Product03

set_option Elab.async false

/-!
# A certified column-vector form for the Lyons representation

The two ATLAS generators preserve the explicit form. Subgroup closure then
propagates preservation to every element of the actual generated carrier.
The existing word-product certificates identify T = (ab)^7; two entries of
F and FT are checked directly to support the scalar restriction.

Source: R. A. Wilson et al., ATLAS LyG1-f5r111B0 and LyG1-max4W1.
Original matrices and programs retain their attribution in `../Atlas111Source/`
and `../Atlas111InvolutionSource/`. Candidate generation is in `source/`.
-/

namespace Lyons.Atlas111LocalFormCertificate
open SimplicityCertificate Atlas111WordCertificate


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transpose_a : atMatrix = atlasAMatrix.transpose := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transpose_b : btMatrix = atlasBMatrix.transpose := by decide +kernel

public theorem ambient_preserves_form (g : LyonsGroup) :
    (matrixRepresentation g).transpose * formMatrix * matrixRepresentation g = formMatrix := by
  have ha : (matrixRepresentation generatorA).transpose * formMatrix *
      matrixRepresentation generatorA = formMatrix := by
    rw [matrixRepresentation_generatorA, ← transpose_a, ← aMatrix_eq, mul_atf, mul_ata]
  have hb : (matrixRepresentation generatorB).transpose * formMatrix *
      matrixRepresentation generatorB = formMatrix := by
    rw [matrixRepresentation_generatorB, ← transpose_b, ← bMatrix_eq, mul_btf, mul_btb]
  have hg : g ∈ Subgroup.closure ({generatorA, generatorB} : Set LyonsGroup) := by
    rw [OrderCertificate.closure_generators]
    trivial
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ha
    · rcases hx with rfl
      exact hb
  | one => simp only [map_one, Matrix.transpose_one, one_mul, mul_one]
  | mul x y hx hy ihx ihy =>
    simp only [map_mul, Matrix.transpose_mul]
    calc
      _ = (matrixRepresentation y).transpose *
          ((matrixRepresentation x).transpose * formMatrix * matrixRepresentation x) *
          matrixRepresentation y := by simp only [Matrix.mul_assoc]
      _ = formMatrix := by rw [ihx, ihy]
  | inv x hx ih =>
    calc
      _ = (matrixRepresentation x⁻¹).transpose *
          ((matrixRepresentation x).transpose * formMatrix * matrixRepresentation x) *
          matrixRepresentation x⁻¹ := by rw [ih]
      _ = (matrixRepresentation x * matrixRepresentation x⁻¹).transpose * formMatrix *
          (matrixRepresentation x * matrixRepresentation x⁻¹) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = formMatrix := by rw [← map_mul, mul_inv_cancel, map_one]; simp

private theorem t_matrix : matrixRepresentation involutionLocalT = ab7Matrix := by
  have h2 : abMatrix ^ 2 = ab2Matrix := (pow_two _).trans mul_ab2
  have h3 : abMatrix ^ 3 = ab3Matrix := by
    rw [show 3 = 2 + 1 from rfl, pow_succ, h2, mul_ab3]
  have h6 : abMatrix ^ 6 = ab6Matrix := by
    rw [show 6 = 3 * 2 from rfl, pow_mul, h3, pow_two, mul_ab6]
  have h7 : abMatrix ^ 7 = ab7Matrix := by
    rw [show 7 = 6 + 1 from rfl, pow_succ, h6, mul_ab7]
  simpa only [involutionLocalT, map_pow, map_mul, matrixRepresentation_generatorA,
    matrixRepresentation_generatorB, ← aMatrix_eq, ← bMatrix_eq, mul_ab] using h7

public theorem form_00 : formMatrix 0 0 = 1 := by decide +kernel
public theorem form_01 : formMatrix 0 1 = 3 := by decide +kernel

public theorem form_t_00 : (formMatrix * matrixRepresentation involutionLocalT) 0 0 = 0 := by
  rw [t_matrix]
  decide +kernel

public theorem form_t_01 : (formMatrix * matrixRepresentation involutionLocalT) 0 1 = 1 := by
  rw [t_matrix]
  decide +kernel

end Lyons.Atlas111LocalFormCertificate
