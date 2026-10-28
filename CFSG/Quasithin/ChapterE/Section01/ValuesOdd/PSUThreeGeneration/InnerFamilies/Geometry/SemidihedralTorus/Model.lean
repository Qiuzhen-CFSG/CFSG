module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.SemidihedralTorus.Coordinates
public import Theory.SpecificGroups.SU3.EvenInnerCentralizers.Torus
public import Theory.SpecificGroups.SU3.FullCentralizer

/-!
# A concrete inverted torus in the projective unitary group

For a norm-one field unit k, put a=(k+k⁻¹)/2 and b=(k-k⁻¹)/2. The matrix
[[a,0,b],[0,1,0],[b,0,a]] is special unitary for the identity Hermitian form.
These matrices form an injective projective image of the norm-one group:
the middle coordinate eliminates the entire scalar kernel. The image is
cyclic of order p+1, is inverted by diag(-1,-1,1), and is preserved by every
diagonal sign change and by the stored field involution.

This constructs the torus for the p ≡ 1 modulo four branch of
Aschbacher--Smith E.1.14(7), printed p.214; compare A.3.21, printed p.55.
Putting the actual ambient four-group centralizer in these coordinates is
an additional theorem, not a premise discharged in this module.
-/

public section

open Matrix Subgroup BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.HermitianForm.EvenInner
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.SemidihedralTorus
variable {F : Type*} [Field F]

private def rotation (a : Fˣ) : Matrix (Fin 3) (Fin 3) F :=
  !![((a : F) + (a : F)⁻¹) / 2, 0, ((a : F) - (a : F)⁻¹) / 2;
     0, 1, 0;
     ((a : F) - (a : F)⁻¹) / 2, 0, ((a : F) + (a : F)⁻¹) / 2]

private theorem rotation_one (h2 : (2 : F) ≠ 0) : rotation (1 : Fˣ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [rotation, h2]

private theorem rotation_mul (h2 : (2 : F) ≠ 0) (a b : Fˣ) :
    rotation (a * b) = rotation a * rotation b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp <;> ring

private def rotationHom (h2 : (2 : F) ≠ 0) : Fˣ →* GL (Fin 3) F where
  toFun a :=
    { val := rotation a
      inv := rotation a⁻¹
      val_inv := by rw [← rotation_mul h2, mul_inv_cancel, rotation_one h2]
      inv_val := by rw [← rotation_mul h2, inv_mul_cancel, rotation_one h2] }
  map_one' := Units.ext (rotation_one h2)
  map_mul' a b := Units.ext (rotation_mul h2 a b)

private theorem rotation_det (h2 : (2 : F) ≠ 0) (a : Fˣ) : (rotation a).det = 1 := by
  simp [rotation, Matrix.det_fin_three]
  field_simp
  ring

private theorem rotation_adjoint (J : HermitianForm 3 F) (a : normOne J) :
    J.conjTranspose (rotation a.val) = rotation a.val⁻¹ := by
  have ha : J.conj (a.val : F) = (a.val : F)⁻¹ := a.property
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, HermitianForm.conjTranspose, map_div₀, map_ofNat, ha]

private theorem rotation_special (J : HermitianForm 3 F) (hJ : J.form = 1)
    (h2 : (2 : F) ≠ 0) (a : normOne J) :
    rotationHom h2 a.val ∈ J.specialSubgroup := by
  rw [J.mem_specialSubgroup_iff]
  constructor
  · change J.conjTranspose (rotation a.val) * J.form * rotation a.val = J.form
    rw [hJ, mul_one, rotation_adjoint, ← rotation_mul h2, inv_mul_cancel, rotation_one h2]
  · apply Units.ext
    exact rotation_det h2 a.val

private def specialRotation (J : HermitianForm 3 F) (hJ : J.form = 1) (h2 : (2 : F) ≠ 0) :
    normOne J →* J.specialSubgroup :=
  ((rotationHom h2).comp (normOne J).subtype).codRestrict _ (rotation_special J hJ h2)

/-- The actual projective image of the two-coordinate norm-one rotations. -/
def projectiveRotation (J : HermitianForm 3 F) (hJ : J.form = 1) (h2 : (2 : F) ≠ 0) :
    normOne J →* ProjectiveSpecialUnitaryMatrixGroup J :=
  J.specialToProjective.comp (specialRotation J hJ h2)

private theorem projectiveRotation_val (J : HermitianForm 3 F)
    (hJ : J.form = 1) (h2 : (2 : F) ≠ 0) (a : normOne J) :
    (projectiveRotation J hJ h2 a).val = ProjGenLinGroup.mk (rotationHom h2 a.val) := by
  change (J.specialToProjective (specialRotation J hJ h2 a)).val = _
  rw [J.specialToProjective_apply_val]
  rfl

/-- The fixed middle coordinate forces a scalar rotation to be the identity. -/
theorem projectiveRotation_injective (J : HermitianForm 3 F) (hJ : J.form = 1)
    (h2 : (2 : F) ≠ 0) : Function.Injective (projectiveRotation J hJ h2) := by
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  have he : ProjGenLinGroup.mk (rotationHom h2 a.val) = 1 := by
    simpa only [projectiveRotation_val, Subgroup.coe_one] using congrArg Subtype.val ha
  obtain ⟨c, hc⟩ := GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp
    (ProjGenLinGroup.mk_eq_one.mp he)
  have h11 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 1 1) hc
  have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 0) hc
  have h02 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 2) hc
  change c = 1 at h11
  have hsum : (a.val : F) = 1 := by
    simp [rotationHom, rotation, Matrix.scalar_apply, h11] at h00 h02
    apply mul_left_cancel₀ h2
    field_simp at h00 h02
    linear_combination h00 - h02
  exact Subtype.ext (Units.ext hsum)

/-- The projective torus retains order p+1, including its cubic part. -/
theorem projectiveRotation_card [Finite F] (J : HermitianForm 3 F) (hJ : J.form = 1)
    (h2 : (2 : F) ≠ 0) {p : ℕ} (hcard : Nat.card F = p ^ 2)
    (hc : ∀ x, J.conj x = x ^ p) :
    Nat.card (projectiveRotation J hJ h2).range = p + 1 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective
    (projectiveRotation_injective J hJ h2)).toEquiv]
  exact normOne_card J hcard hc

private theorem standard_inverts_rotation (J : HermitianForm 3 F) (hJ : J.form = 1)
    (h2 : (2 : F) ≠ 0) (a : normOne J) :
    Matrix.SU3.standardInvolution J hJ * specialRotation J hJ h2 a *
      (Matrix.SU3.standardInvolution J hJ)⁻¹ = specialRotation J hJ h2 a⁻¹ := by
  have hz : (Matrix.SU3.standardInvolution J hJ)⁻¹ = Matrix.SU3.standardInvolution J hJ :=
    inv_eq_iff_mul_eq_one.mpr (by
      rw [← pow_two]
      exact Matrix.SU3.standardInvolution_sq J hJ)
  rw [hz]
  apply Subtype.ext
  apply Units.ext
  change !![-1, 0, 0; 0, -1, 0; 0, 0, 1] * rotation a.val *
    !![-1, 0, 0; 0, -1, 0; 0, 0, 1] = rotation a⁻¹.val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

private theorem sign_conjugates_rotation (h2 : (2 : F) ≠ 0) (ε : Fin 3 → Bool) (a : Fˣ) :
    signGL ε * rotationHom h2 a * (signGL ε)⁻¹ =
      rotationHom h2 (if ε 0 = ε 2 then a else a⁻¹) := by
  apply Units.ext
  ext i j
  cases h0 : ε 0 <;> cases h1 : ε 1 <;> cases h2' : ε 2 <;>
    fin_cases i <;> fin_cases j <;>
    simp [signGL, UnitaryThree.OddTorusNormalizer.diagonalHom, rotationHom,
      rotation, Matrix.mul_apply, Fin.sum_univ_three, h0, h1, h2'] <;> ring

private theorem conjugation_maps_rotation (J : HermitianForm 3 F)
    (h2 : (2 : F) ≠ 0) (a : normOne J) :
    GeneralLinearGroup.map J.conj.toRingHom (rotationHom h2 a.val) =
      rotationHom h2 a.val⁻¹ := by
  apply Units.ext
  have ha : J.conj (a.val : F) = (a.val : F)⁻¹ := a.property
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotationHom, rotation, map_div₀, map_ofNat, ha]

/-- Every actor with the specified sign/Frobenius formula preserves the torus. -/
theorem rotation_preserved_of_signSemilinear (J : HermitianForm 3 F)
    (hJ : J.form = 1) (h2 : (2 : F) ≠ 0)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : HasSignSemilinearForm J a) :
    ∀ x ∈ (projectiveRotation J hJ h2).range,
      a x ∈ (projectiveRotation J hJ h2).range := by
  obtain ⟨ε, σ, hσ, ha⟩ := ha
  rintro x ⟨k, rfl⟩
  have hsign (k : normOne J) :
      ProjGenLinGroup.mk (signGL ε) * (projectiveRotation J hJ h2 k).val *
        (ProjGenLinGroup.mk (signGL ε))⁻¹ =
          (projectiveRotation J hJ h2 (if ε 0 = ε 2 then k else k⁻¹)).val := by
    simp only [projectiveRotation_val]
    rw [← map_inv, ← map_mul, ← map_mul, sign_conjugates_rotation]
    split_ifs <;> rfl
  rcases hσ with rfl | rfl
  · refine ⟨if ε 0 = ε 2 then k else k⁻¹, ?_⟩
    apply Subtype.ext
    rw [ha]
    change _ = ProjGenLinGroup.mk (signGL ε) *
      ProjGenLinGroup.map (RingHom.id F) _ * (ProjGenLinGroup.mk (signGL ε))⁻¹
    simpa only [ProjGenLinGroup.map_id, MonoidHom.id_apply] using (hsign k).symm
  · refine ⟨if ε 0 = ε 2 then k⁻¹ else k, ?_⟩
    apply Subtype.ext
    rw [ha]
    have hf : ProjGenLinGroup.map J.conj.toRingHom (projectiveRotation J hJ h2 k).val =
        (projectiveRotation J hJ h2 k⁻¹).val := by
      rw [projectiveRotation_val, projectiveRotation_val,
        ProjGenLinGroup.map_mk, conjugation_maps_rotation]
      rfl
    rw [hf]
    simpa using (hsign k⁻¹).symm

/-- The torus is cyclic as an image of the field norm-one group. -/
theorem projectiveRotation_isCyclic [Finite F] (J : HermitianForm 3 F)
    (hJ : J.form = 1) (h2 : (2 : F) ≠ 0) :
    IsCyclic (projectiveRotation J hJ h2).range := by
  exact isCyclic_of_surjective (projectiveRotation J hJ h2).rangeRestrict
    (projectiveRotation J hJ h2).rangeRestrict_surjective

/-- The standard projective involution inverts the full torus. -/
theorem projectiveRotation_inverted (J : HermitianForm 3 F)
    (hJ : J.form = 1) (h2 : (2 : F) ≠ 0) :
    ∀ x ∈ (projectiveRotation J hJ h2).range,
      J.specialToProjective (Matrix.SU3.standardInvolution J hJ) * x *
        (J.specialToProjective (Matrix.SU3.standardInvolution J hJ))⁻¹ = x⁻¹ := by
  rintro x ⟨a, rfl⟩
  have h := congrArg J.specialToProjective (standard_inverts_rotation J hJ h2 a)
  simpa only [projectiveRotation, MonoidHom.comp_apply, map_mul, map_inv] using h
end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.SemidihedralTorus
