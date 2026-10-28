module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.TwoLocalCover.FixedRadical

/-!
# Scalar determinant correction in unitary four-space

Over a finite field of characteristic two, fourth powering is an automorphism.
For a unitary matrix A choose c with c⁴ = det(A)⁻¹. The unitary equation gives
norm(det(A)) = 1, so injectivity of fourth powering gives norm(c) = 1.
Consequently cA is special unitary and has the same image as A on every
subspace. This reduces SU₄ transitivity to genuine unitary basis construction,
including the field of four elements. It applies also to maximal isotropic
planes, whose perpendicular has no nonzero nondegenerate subspace.

Source: determinant correction in GLS3, Lemma 2.7.2, printed pp.89–90,
`refs/KGroup/GLS3/chapter2.tex`; the scalar correction uses the specific
four-dimensional characteristic-two setting.
-/

open Matrix BenderSuzuki.MatrixGroups
public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.TwoLocalCover
variable {F : Type*} [Field F] (J : HermitianForm 4 F)

private theorem norm_det (A : GL (Fin 4) F) (hA : A ∈ J.unitarySubgroup) :
    J.conj A.val.det * A.val.det = 1 := by
  have he : (J.conjTranspose A.val).det = J.conj A.val.det := by
    change (A.val.map J.conj).transpose.det = J.conj A.val.det
    rw [det_transpose, J.conj.map_det]
    rfl
  have hd := congrArg Matrix.det ((J.mem_unitarySubgroup_iff A).mp hA)
  simp only [det_mul, he] at hd
  apply (mul_right_cancel₀ J.form_nondegenerate)
  calc
    (J.conj A.val.det * A.val.det) * J.form.det =
      J.conj A.val.det * J.form.det * A.val.det := by ring
    _ = 1 * J.form.det := by simpa using hd

private theorem scalar_unitary (u : Fˣ) (hu : J.conj u.val * u.val = 1) :
    GeneralLinearGroup.scalar (Fin 4) u ∈ J.unitarySubgroup := by
  rw [J.mem_unitarySubgroup_iff]
  have he : J.conjTranspose (GeneralLinearGroup.scalar (Fin 4) u).val =
      diagonal (fun _ : Fin 4 => J.conj u.val) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [HermitianForm.conjTranspose, GeneralLinearGroup.scalar]
    · simp [HermitianForm.conjTranspose, GeneralLinearGroup.scalar, hij, Ne.symm]
  rw [he]
  change diagonal _ * J.form * diagonal (fun _ : Fin 4 => u.val) = J.form
  ext i j
  simp only [mul_diagonal, diagonal_mul]
  calc
    J.conj u.val * J.form i j * u.val = (J.conj u.val * u.val) * J.form i j := by ring
    _ = J.form i j := by rw [hu, one_mul]

/-- In characteristic two, multiplying by a scalar corrects the determinant
without changing the image of any subspace. -/
theorem exists_special_same_subspace_images [Finite F] [CharP F 2]
    (A : GL (Fin 4) F) (hA : A ∈ J.unitarySubgroup) :
    ∃ g : J.specialSubgroup, ∀ W : Submodule F (Fin 4 → F),
      W.map A.val.mulVecLin = W.map (linearAction J g).toLinearMap := by
  let φ := iterateFrobeniusEquiv F 2 2
  obtain ⟨c, hc⟩ := φ.surjective A.val.det⁻¹
  have hc4 : c ^ 4 = A.val.det⁻¹ := hc
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hc4
    exact (inv_ne_zero (GeneralLinearGroup.det_ne_zero A)) hc4.symm
  have hcN : J.conj c * c = 1 := by
    apply φ.injective
    change (J.conj c * c) ^ 4 = (1 : F) ^ 4
    rw [mul_pow, ← map_pow, hc4, map_inv₀, ← mul_inv, norm_det J A hA, inv_one, one_pow]
  let u : Fˣ := Units.mk0 c hc0
  let B := GeneralLinearGroup.scalar (Fin 4) u * A
  have hB : B ∈ J.specialSubgroup := by
    change B ∈ J.unitarySubgroup ∧ GeneralLinearGroup.det B = 1
    refine ⟨J.unitarySubgroup.mul_mem (scalar_unitary J u hcN) hA, ?_⟩
    apply Units.ext
    change (GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 4) u * A)).val = 1
    rw [map_mul, GeneralLinearGroup.det_scalar, Units.val_mul]
    change c ^ 4 * A.val.det = 1
    rw [hc4, inv_mul_cancel₀ (GeneralLinearGroup.det_ne_zero A)]
  refine ⟨⟨B, hB⟩, ?_⟩
  intro W
  have hact (v : Fin 4 → F) : linearAction J ⟨B, hB⟩ v = c • (A.val *ᵥ v) := by
    change ((GeneralLinearGroup.scalar (Fin 4) u).val * A.val) *ᵥ v = _
    rw [← mulVec_mulVec]
    exact diagonal_const_mulVec _ _
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨c⁻¹ • w, W.smul_mem _ hw, ?_⟩
    change linearAction J ⟨B, hB⟩ (c⁻¹ • w) = A.val *ᵥ w
    rw [hact, mulVec_smul, smul_smul, mul_inv_cancel₀ hc0, one_smul]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨c • w, W.smul_mem _ hw, ?_⟩
    change A.val *ᵥ (c • w) = linearAction J ⟨B, hB⟩ w
    rw [hact, mulVec_smul]

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.TwoLocalCover
