module

public import BenderSuzuki.MatrixGroups.Unitary
public import Theory.SpecificGroups.SL3.InvolutionBlock
/-!
# Full standard-involution centralizers in SU₃

For identity-Gram Hermitian forms in dimensions three and two with the same
stored field involution, the determinant-corrected block embedding
`A ↦ diag(A, det(A)⁻¹)` identifies the full two-dimensional unitary group
with the centralizer of `diag(-1,-1,1)` in the actual special unitary group.
Only characteristic different from two is needed for the centralizer result.

The unitary equation on the block is equivalent to the two-dimensional
unitary equation: its determinant gives the norm-one equation for the final
coordinate. The published SL₃ block-centralizer theorem then proves fullness.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma A.3.21(a), printed p. 55 (PDF p. 66).
-/

public section

open Matrix
open scoped Matrix
open BenderSuzuki.MatrixGroups
namespace Matrix.SU3
variable {F : Type*} [Field F]

theorem unitary_det_norm {n : ℕ} (J : HermitianForm n F) (hJ : J.form = 1)
    (A : J.unitarySubgroup) : J.conj A.val.val.det * A.val.val.det = 1 := by
  have h := A.property
  rw [J.mem_unitarySubgroup_iff, hJ, mul_one] at h
  have hd := congrArg Matrix.det h
  change ((A.val.val.map J.conj).transpose * A.val.val).det = (1 : Matrix (Fin n) (Fin n) F).det at hd
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hd
  change (J.conj.mapMatrix A.val.val).det * A.val.val.det = 1 at hd
  rw [← J.conj.map_det] at hd
  exact hd

/-- The actual special unitary matrix `diag(-1,-1,1)`. -/
@[expose] def standardInvolution (J : HermitianForm 3 F) (hJ : J.form = 1) :
    J.specialSubgroup :=
  ⟨SpecialLinearGroup.toGL (SL3.standardInvolution F), by
    rw [J.mem_specialSubgroup_iff, hJ]
    constructor
    · change J.conjTranspose (SL3.standardInvolution F).val * 1 *
        (SL3.standardInvolution F).val = 1
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [HermitianForm.conjTranspose, SL3.standardInvolution, Matrix.mul_apply,
          Fin.sum_univ_three]
    · simp⟩

theorem standardInvolution_sq (J : HermitianForm 3 F) (hJ : J.form = 1) :
    standardInvolution J hJ ^ 2 = 1 := by
  apply Subtype.ext
  change SpecialLinearGroup.toGL (SL3.standardInvolution F) ^ 2 = 1
  rw [← map_pow, SL3.standardInvolution_sq, map_one]

theorem standardInvolution_orderOf (J : HermitianForm 3 F) (hJ : J.form = 1)
    (h2 : (2 : F) ≠ 0) : orderOf (standardInvolution J hJ) = 2 := by
  apply orderOf_eq_prime (standardInvolution_sq J hJ)
  intro h
  have hval := congrArg (fun A : J.specialSubgroup => A.val) h
  have he : SL3.standardInvolution F = 1 := SpecialLinearGroup.toGL_injective (hval.trans (map_one _).symm)
  have hh := SL3.standardInvolution_orderOf F h2
  rw [he, orderOf_one] at hh
  contradiction

private def toSL (J : HermitianForm 3 F) : J.specialSubgroup →* SpecialLinearGroup (Fin 3) F where
  toFun A := ⟨A.val.val, by
    have h := (J.mem_specialSubgroup_iff A.val).mp A.property
    exact congrArg Units.val h.2⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

private theorem toSL_injective (J : HermitianForm 3 F) : Function.Injective (toSL J) := by
  intro A B h
  exact Subtype.ext (Units.ext (congrArg Subtype.val h))

theorem block_unitary_iff (J3 : HermitianForm 3 F) (J2 : HermitianForm 2 F)
    (h3 : J3.form = 1) (h2 : J2.form = 1) (hc : J3.conj = J2.conj)
    (A : GL (Fin 2) F) :
    SpecialLinearGroup.toGL (SL3.blockEmbedding F A) ∈ J3.unitarySubgroup ↔
      A ∈ J2.unitarySubgroup := by
  rw [J3.mem_unitarySubgroup_iff, J2.mem_unitarySubgroup_iff, h3, h2, mul_one, mul_one]
  change J3.conjTranspose (SL3.blockMatrix F A) * SL3.blockMatrix F A = 1 ↔ _
  constructor
  · intro h
    ext i j
    have he (i j : Fin 3) := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M i j) h
    fin_cases i <;> fin_cases j
    · simpa [SL3.blockMatrix, HermitianForm.conjTranspose,
        Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, hc] using he 0 0
    · simpa [SL3.blockMatrix, HermitianForm.conjTranspose,
        Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, hc] using he 0 1
    · simpa [SL3.blockMatrix, HermitianForm.conjTranspose,
        Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, hc] using he 1 0
    · simpa [SL3.blockMatrix, HermitianForm.conjTranspose,
        Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, hc] using he 1 1
  · intro h
    have hA : A ∈ J2.unitarySubgroup := by
      rw [J2.mem_unitarySubgroup_iff, h2, mul_one]
      exact h
    have hd := unitary_det_norm J2 h2 ⟨A, hA⟩
    have hi : J2.conj A.val.det⁻¹ * A.val.det⁻¹ = 1 := by
      rw [map_inv₀, ← mul_inv, hd, inv_one]
    have he (i j : Fin 2) := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M i j) h
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SL3.blockMatrix, HermitianForm.conjTranspose,
        Matrix.mul_apply, Fin.sum_univ_three, hc]
    · simpa [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_two] using he 0 0
    · simpa [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_two] using he 0 1
    · simpa [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_two] using he 1 0
    · simpa [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_two] using he 1 1
    · simpa only [map_inv₀] using hi

/-- The determinant-corrected block embedding into the actual SU₃. -/
@[expose] def blockEmbedding (J3 : HermitianForm 3 F) (J2 : HermitianForm 2 F)
    (h3 : J3.form = 1) (h2 : J2.form = 1) (hc : J3.conj = J2.conj) :
    J2.unitarySubgroup →* J3.specialSubgroup :=
  ((SpecialLinearGroup.toGL.comp (SL3.blockEmbedding F)).comp J2.unitarySubgroup.subtype).codRestrict J3.specialSubgroup (by
      intro A
      exact ⟨(block_unitary_iff J3 J2 h3 h2 hc A.val).mpr A.property, by simp⟩)

private theorem toSL_blockEmbedding (J3 : HermitianForm 3 F) (J2 : HermitianForm 2 F)
    (h3 : J3.form = 1) (h2 : J2.form = 1) (hc : J3.conj = J2.conj)
    (A : J2.unitarySubgroup) :
    toSL J3 (blockEmbedding J3 J2 h3 h2 hc A) = SL3.blockEmbedding F A.val := by rfl

theorem blockEmbedding_injective (J3 : HermitianForm 3 F) (J2 : HermitianForm 2 F)
    (h3 : J3.form = 1) (h2 : J2.form = 1) (hc : J3.conj = J2.conj) :
    Function.Injective (blockEmbedding J3 J2 h3 h2 hc) := by
  intro A B h
  apply Subtype.ext
  apply SL3.blockEmbedding_injective F
  exact congrArg (toSL J3) h

theorem blockEmbedding_range (J3 : HermitianForm 3 F) (J2 : HermitianForm 2 F)
    (h3 : J3.form = 1) (h2 : J2.form = 1) (hc : J3.conj = J2.conj)
    (hchar : (2 : F) ≠ 0) :
    (blockEmbedding J3 J2 h3 h2 hc).range =
      Subgroup.centralizer ({standardInvolution J3 h3} : Set J3.specialSubgroup) := by
  ext A
  have hcent : A ∈ Subgroup.centralizer ({standardInvolution J3 h3} : Set J3.specialSubgroup) ↔
      toSL J3 A ∈ Subgroup.centralizer ({SL3.standardInvolution F} :
        Set (SpecialLinearGroup (Fin 3) F)) := by
    simp only [Subgroup.mem_centralizer_singleton_iff]
    rw [← (toSL_injective J3).eq_iff]
    simp only [map_mul]
    rfl
  rw [hcent, ← SL3.blockEmbedding_range F hchar]
  constructor
  · rintro ⟨B, rfl⟩
    exact ⟨B.val, rfl⟩
  · rintro ⟨B, hB⟩
    have hGL : SpecialLinearGroup.toGL (SL3.blockEmbedding F B) = A.val :=
      Units.ext (congrArg Subtype.val hB)
    have hBU : B ∈ J2.unitarySubgroup :=
      (block_unitary_iff J3 J2 h3 h2 hc B).mp (hGL ▸ A.property.1)
    refine ⟨⟨B, hBU⟩, ?_⟩
    apply toSL_injective J3
    exact hB

/-- The full standard-involution centralizer is the actual GU₂. -/
noncomputable def standardInvolutionCentralizerEquiv
    (J3 : HermitianForm 3 F) (J2 : HermitianForm 2 F)
    (h3 : J3.form = 1) (h2 : J2.form = 1) (hc : J3.conj = J2.conj)
    (hchar : (2 : F) ≠ 0) :
    J2.unitarySubgroup ≃*
      Subgroup.centralizer ({standardInvolution J3 h3} : Set J3.specialSubgroup) :=
  (MonoidHom.ofInjective (blockEmbedding_injective J3 J2 h3 h2 hc)).trans
    (MulEquiv.subgroupCongr (blockEmbedding_range J3 J2 h3 h2 hc hchar))

theorem standardInvolutionCentralizerEquiv_apply_val
    (J3 : HermitianForm 3 F) (J2 : HermitianForm 2 F)
    (h3 : J3.form = 1) (h2 : J2.form = 1) (hc : J3.conj = J2.conj)
    (hchar : (2 : F) ≠ 0) (A : J2.unitarySubgroup) :
    (standardInvolutionCentralizerEquiv J3 J2 h3 h2 hc hchar A).val =
      blockEmbedding J3 J2 h3 h2 hc A := by rfl
/-- The representative has exactly the advertised diagonal matrix. -/
theorem standardInvolution_val (J : HermitianForm 3 F) (hJ : J.form = 1) :
    (standardInvolution J hJ).val.val = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by rfl

/-- The centralizer embedding is given by the determinant-corrected block matrix. -/
theorem blockEmbedding_val (J3 : HermitianForm 3 F) (J2 : HermitianForm 2 F)
    (h3 : J3.form = 1) (h2 : J2.form = 1) (hc : J3.conj = J2.conj)
    (A : J2.unitarySubgroup) :
    (blockEmbedding J3 J2 h3 h2 hc A).val.val = SL3.blockMatrix F A.val := by rfl

end Matrix.SU3
end
