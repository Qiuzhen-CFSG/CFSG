module

public import Theory.Representation.HermitianTensorThree.ImageOuter.Normalizer.Actions
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

/-!
# The PGL₃(4) extension of the Hermitian tensor image

For the field of order four every nonzero scalar has norm one. Thus the
congruence kernel is the entire GL₃ center, giving an actual equivalence with
PGL₃(4). The equivalence commutes with both the GL₃ quotient map and the
published PSL₃ identification of the SL₃ image.

This supplies the concrete inner-diagonal extension in Aschbacher–Smith,
combined manuscript of 1 March 2004, H.4.6(3), printed p.382.
-/

@[expose] public section
noncomputable section
namespace Representation.HermitianTensorThree.ImageOuter

theorem binaryCongruence_ker_one :
    (binaryCongruence 1).ker = Subgroup.center (Matrix.GeneralLinearGroup (Fin 3) (E 1)) := by
  ext g
  rw [mem_binaryCongruence_ker_iff, Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  constructor
  · rintro ⟨c, hc, _⟩; exact ⟨c, hc.symm⟩
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      intro hz
      have hdet := Matrix.GeneralLinearGroup.det_ne_zero g
      rw [← hc, hz] at hdet
      simp [Matrix.scalar_apply] at hdet
    have hc3 : c ^ 3 = 1 := by
      let : Fintype (E 1) := Fintype.ofFinite _
      have h := FiniteField.pow_card_sub_one_eq_one c hc0
      simpa only [← Nat.card_eq_fintype_card, card_E, show 2 ^ (2 * 1) - 1 = 3 by decide] using h
    exact ⟨c, hc.symm, norm_cube_root_odd 1 (by decide) c hc3⟩

/-- The actual GL₃(E 1) congruence image is PGL₃(E 1). -/
def congruenceImageEquivPGL : congruenceImage 1 ≃* Matrix.ProjGenLinGroup (Fin 3) (E 1) :=
  (QuotientGroup.quotientKerEquivRange (binaryCongruence 1)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq binaryCongruence_ker_one)

theorem congruenceImageEquivPGL_toCongruenceImage
    (g : Matrix.GeneralLinearGroup (Fin 3) (E 1)) :
    congruenceImageEquivPGL (toCongruenceImage 1 g) = Matrix.ProjGenLinGroup.mk g := by
  have he : (QuotientGroup.quotientKerEquivRange (binaryCongruence 1)).symm
      (toCongruenceImage 1 g) = QuotientGroup.mk g :=
    (QuotientGroup.quotientKerEquivRange (binaryCongruence 1)).symm_apply_apply (QuotientGroup.mk g)
  change (QuotientGroup.quotientMulEquivOfEq binaryCongruence_ker_one)
    ((QuotientGroup.quotientKerEquivRange (binaryCongruence 1)).symm
      (toCongruenceImage 1 g)) = _
  rw [he]; rfl

/-- Compatibility with the published PSL₃ identification and the natural PSL→PGL inclusion. -/
theorem congruenceImageEquivPGL_image (g : Image 1) :
    congruenceImageEquivPGL (imageToCongruenceImage 1 g) =
      Matrix.ProjectiveSpecialLinearGroup.toPGL (imageEquivPSL 1 (by decide) g) := by
  obtain ⟨a, ha⟩ := g.property
  have hg : g = toImage 1 a := Subtype.ext ha.symm
  rw [hg, imageToCongruenceImage_toImage, congruenceImageEquivPGL_toCongruenceImage,
    imageEquivPSL_toImage]
  rfl

end Representation.HermitianTensorThree.ImageOuter
