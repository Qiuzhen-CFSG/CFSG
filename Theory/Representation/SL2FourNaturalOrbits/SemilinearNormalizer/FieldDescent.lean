module

public import Theory.Representation.SL2FourNaturalOrbits.SemilinearNormalizer.Normalizer
public import Theory.Representation.SL2FourNaturalOrbits.SemilinearNormalizer.FixedSpaces
import Mathlib.Tactic.Ring

/-!
# Descent of field-coset involutions on the natural F₄ plane

Every involution in the Frobenius coset of ΓL₂(4) is conjugate by an actual
GL₂(4) matrix to the specified coordinate Frobenius. In the subgroup generated
by SL₂(4) and Frobenius, the conjugator has determinant one. Consequently every
involution outside the SL₂ image in its binary normalizer fixes exactly four
vectors, with the coefficient automorphism deduced from these hypotheses.

For the matrix cocycle A σ(A) = I, use B = c I + σ(c) A. Then A σ(B) = B.
The determinant of B depends only on c, tr(A), and det(A); a small checked
calculation on the sixteen trace–determinant pairs selects c making B
invertible. This avoids enumerating matrix groups or searching for conjugators.
In the specified SL₂–Frobenius subgroup, determinant-label one is fixed, so
σ(det B) = det B, forcing the nonzero determinant to be one.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the natural-module
and field-type calculations in 6.2.5, printed pp.680--681 (PDF pp.697--698).
The ambient fusion and full plane-orbit conclusions remain with their assembly.
-/

public section
noncomputable section
namespace Representation.SL2FourNatural.SemilinearNormalizer
open Matrix Matrix.GeneralLinearGroup

private theorem scalar_choice (t d : F) :
    ∃ c : F, c ^ 2 + c * fieldFrobenius c * t + (fieldFrobenius c) ^ 2 * d ≠ 0 := by
  revert t d
  decide +kernel

private theorem descent_det (A : Matrix (Fin 2) (Fin 2) F) (c : F) :
    (c • (1 : Matrix (Fin 2) (Fin 2) F) + fieldFrobenius c • A).det =
      c ^ 2 + c * fieldFrobenius c * (A 0 0 + A 1 1) +
        (fieldFrobenius c) ^ 2 * A.det := by
  simp [Matrix.det_fin_two, Matrix.add_apply, Matrix.smul_apply]
  ring

private theorem descent_basis (A : LinearGroup)
    (hA : A * coefficientAction F fieldFrobenius A = 1) :
    ∃ B : LinearGroup, A * coefficientAction F fieldFrobenius B = B := by
  obtain ⟨c, hc⟩ := scalar_choice (A 0 0 + A 1 1) A.val.det
  let M := c • (1 : Matrix (Fin 2) (Fin 2) F) + fieldFrobenius c • A.val
  have hM : M.det ≠ 0 := by rw [descent_det]; exact hc
  refine ⟨mkOfDetNeZero M hM, ?_⟩
  apply Units.ext
  change A.val * M.map fieldFrobenius = M
  have hm : M.map fieldFrobenius =
      fieldFrobenius c • (1 : Matrix (Fin 2) (Fin 2) F) +
        c • A.val.map fieldFrobenius := by
    funext i j
    simp only [M, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, map_add, map_mul, fieldFrobenius_involutive]
    congr 1
    simp [Matrix.one_apply]
  have hAA : A.val * A.val.map fieldFrobenius = 1 := congrArg Units.val hA
  rw [hm, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, mul_one, hAA]
  exact add_comm _ _

/-- Every field-coset involution is GL₂(4)-conjugate to coordinate Frobenius. -/
theorem field_involution_conjugate (g : Gamma) (hr : g.right = fieldFrobenius)
    (h2 : g ^ 2 = 1) :
    ∃ B : LinearGroup, g = SemidirectProduct.inl B * fieldElement *
      (SemidirectProduct.inl B)⁻¹ := by
  have hA : g.left * coefficientAction F fieldFrobenius g.left = 1 := by
    simpa only [pow_two, SemidirectProduct.mul_left, hr, SemidirectProduct.one_left]
      using congrArg SemidirectProduct.left h2
  obtain ⟨B, hB⟩ := descent_basis g.left hA
  refine ⟨B, ?_⟩
  apply (eq_mul_inv_iff_mul_eq).mpr
  apply SemidirectProduct.ext
  · simpa [fieldElement, SemidirectProduct.mul_left, hr] using hB
  · simp [fieldElement, hr]

/-- In the specified SL₂–Frobenius subgroup the conjugator belongs to SL₂(4). -/
theorem special_field_involution_conjugate (g : Gamma) (hg : g ∈ specialFieldGamma)
    (hr : g.right = fieldFrobenius) (h2 : g ^ 2 = 1) :
    ∃ A : SL, g = special A * fieldElement * (special A)⁻¹ := by
  obtain ⟨B, hB⟩ := field_involution_conjugate g hr h2
  have hdg : g.left.val.det = 1 := by
    have h := congrArg Units.val (specialFieldGamma_fixes_one ⟨g, hg⟩)
    simpa [labels_apply] using h
  have hstep : g * SemidirectProduct.inl B = SemidirectProduct.inl B * fieldElement :=
    eq_mul_inv_iff_mul_eq.mp hB
  have hleft : g.left * coefficientAction F fieldFrobenius B = B := by
    simpa [fieldElement, SemidirectProduct.mul_left, hr] using
      congrArg SemidirectProduct.left hstep
  have hdB : fieldFrobenius B.val.det = B.val.det := by
    have h := congrArg (fun A : LinearGroup => A.val.det) hleft
    change (g.left.val * B.val.map fieldFrobenius).det = B.val.det at h
    rw [Matrix.det_mul, hdg, one_mul] at h
    exact (fieldFrobenius.map_det B.val).trans h
  have hB1 : B.val.det = 1 :=
    ((fieldFrobenius_fixed B.val.det).mp hdB).resolve_left (det_ne_zero B)
  let A : SL := ⟨B.val, hB1⟩
  have he : special A = SemidirectProduct.inl B := by
    apply congrArg SemidirectProduct.inl
    apply Units.ext
    rfl
  exact ⟨A, by rw [he]; exact hB⟩

/-- The fixed space of every field-coset involution is a binary plane. -/
theorem card_field_involution_fixed (g : Gamma) (hr : g.right = fieldFrobenius)
    (h2 : g ^ 2 = 1) : Nat.card (natural g).toLinearMap.fixedSubmodule = 4 := by
  obtain ⟨B, rfl⟩ := field_involution_conjugate g hr h2
  rw [map_mul, map_mul, map_inv, natural_fieldElement]
  exact card_conjugate_fieldFixed _

/-- An involution outside the determinant-one linear layer has Frobenius coefficients. -/
theorem field_coefficient_of_involution (g : Gamma) (h2 : g ^ 2 = 1)
    (hg : g ∉ special.range) : g.right = fieldFrobenius := by
  rcases fieldAutomorphism_cases g.right with hr | hr
  · exfalso
    apply hg
    rw [mem_special_range]
    refine ⟨hr, ?_⟩
    have hA : g.left * g.left = 1 := by
      simpa [pow_two, SemidirectProduct.mul_left, hr] using
        congrArg SemidirectProduct.left h2
    apply Units.ext
    apply fieldFrobenius.injective
    have hd := congrArg (fun A : LinearGroup => A.val.det) hA
    simpa [fieldFrobenius_apply, pow_two, Matrix.det_mul] using hd
  · exact hr

/-- The literal normalizer equivalence identifies the coefficient of every involution
outside the natural SL₂ image, without an assumed semilinearity witness. -/
theorem normalizer_involution_coefficients (x : BinaryGL) (hx : x ∈ normalizer)
    (h2 : x ^ 2 = 1) (hSL : x ∉ action.range) :
    (normalizerEquiv.symm ⟨x, hx⟩).right = fieldFrobenius := by
  apply field_coefficient_of_involution
  · apply normalizerEquiv.injective
    apply Subtype.ext
    simpa using h2
  · rintro ⟨A, hA⟩
    apply hSL
    refine ⟨A, ?_⟩
    have h := congrArg (fun g => (normalizerEquiv g : BinaryGL)) hA
    simpa only [normalizerEquiv_apply, natural_special,
      MulEquiv.apply_symm_apply] using h

/-- Every involution outside SL₂ in its binary normalizer is conjugate to coordinate
Frobenius by an actual F₄-linear matrix acting on the original module. -/
theorem normalizer_involution_conjugate (x : BinaryGL) (hx : x ∈ normalizer)
    (h2 : x ^ 2 = 1) (hSL : x ∉ action.range) :
    ∃ B : LinearGroup, x = linear B * frobeniusLinear * (linear B)⁻¹ := by
  let g := normalizerEquiv.symm ⟨x, hx⟩
  have hr : g.right = fieldFrobenius := normalizer_involution_coefficients x hx h2 hSL
  have hg2 : g ^ 2 = 1 := by
    apply normalizerEquiv.injective
    apply Subtype.ext
    simpa [g] using h2
  obtain ⟨B, hB⟩ := field_involution_conjugate g hr hg2
  refine ⟨B, ?_⟩
  have he : natural g = x := congrArg Subtype.val (normalizerEquiv.apply_symm_apply ⟨x, hx⟩)
  rw [← he, hB, map_mul, map_mul, map_inv, natural_fieldElement]
  rfl

/-- Every involution outside the SL₂ image in the binary normalizer fixes exactly
four vectors of the original natural module. -/
theorem card_normalizer_involution_fixed (x : BinaryGL) (hx : x ∈ normalizer)
    (h2 : x ^ 2 = 1) (hSL : x ∉ action.range) :
    Nat.card x.toLinearMap.fixedSubmodule = 4 := by
  obtain ⟨B, rfl⟩ := normalizer_involution_conjugate x hx h2 hSL
  exact card_conjugate_fieldFixed _

/-- For the actual binary subgroup generated by SL₂ and Frobenius, every involution
outside SL₂ has a conjugator in the original SL₂ action. -/
theorem specialField_involution_conjugate (x : BinaryGL) (hx : x ∈ specialField)
    (h2 : x ^ 2 = 1) (hSL : x ∉ action.range) :
    ∃ A : SL, x = action A * frobeniusLinear * (action A)⁻¹ := by
  rw [← specialFieldGamma_map_natural] at hx
  obtain ⟨g, hg, rfl⟩ := hx
  have hg2 : g ^ 2 = 1 := by
    apply natural_injective
    simpa only [map_pow, map_one] using h2
  have hgs : g ∉ special.range := by
    rintro ⟨A, rfl⟩
    exact hSL ⟨A, (natural_special A).symm⟩
  obtain ⟨A, hA⟩ := special_field_involution_conjugate g hg
    (field_coefficient_of_involution g hg2 hgs) hg2
  refine ⟨A, ?_⟩
  rw [hA, map_mul, map_mul, map_inv, natural_special, natural_fieldElement]

end Representation.SL2FourNatural.SemilinearNormalizer
