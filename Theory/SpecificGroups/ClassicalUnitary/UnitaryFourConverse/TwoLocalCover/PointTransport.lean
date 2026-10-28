module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.TwoLocalCover.FixedRadical
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFormTransport

/-!
# Unitary transport of isotropic points in Hermitian four-space

Every isotropic line for the antidiagonal Hermitian form is the image of the
coordinate point under an actual unitary matrix. For an isotropic vector `w`,
the map `x ↦ x + pairing J w x • w` is an involutory unitary transvection in
characteristic two. Two isotropic vectors with nonzero pairing can be scaled
to pair to one, and the transvection along their sum maps one to the other.
If the target is perpendicular to the coordinate point, an explicit isotropic
coordinate vector has nonzero pairing with both, so two transvections suffice.

This proves the isotropic-point instance of Witt extension (GLS3, Lemma 2.7.1,
printed p.89, `refs/KGroup/GLS3/chapter2.tex`) used in the classical two-local
argument on printed p.115 of `refs/KGroup/GLS3/chapter3.tex`. The construction
only needs characteristic two and an involution, and therefore includes `n = 1`
under the stated finite-field hypotheses. Determinant correction and the
unconditional two-local cover are separate from this geometric result.
-/

noncomputable section

open Matrix BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.TwoLocalCover
variable {F : Type*} [Field F]
local notation "V" => (Fin 4 → F)

private def pointTransvection (J : HermitianForm 4 F) (w : V) : V →ₗ[F] V :=
  LinearMap.id + (pairingMap J w).smulRight w

private lemma pointTransvection_apply (J : HermitianForm 4 F) (w x : V) :
    pointTransvection J w x = x + pairing J w x • w := rfl

variable [CharP F 2]

private lemma pointTransvection_involutive (J : HermitianForm 4 F) (w : V)
    (hw : pairing J w w = 0) : Function.Involutive (pointTransvection J w) := by
  intro x
  simp only [pointTransvection_apply, pairing_add_right, pairing_smul_right, hw,
    mul_zero, add_zero]
  rw [add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]

private lemma pointTransvection_isometry (J : HermitianForm 4 F) (w : V)
    (hw : pairing J w w = 0) (x y : V) :
    pairing J (pointTransvection J w x) (pointTransvection J w y) = pairing J x y := by
  simp only [pointTransvection_apply, pairing_add_left, pairing_add_right,
    pairing_smul_left, pairing_smul_right, hw, mul_zero, add_zero, pairing_conj]
  rw [mul_comm (pairing J w y), add_assoc, CharTwo.add_self_eq_zero, add_zero]

private def pointTransvectionGL (J : HermitianForm 4 F) (w : V)
    (hw : pairing J w w = 0) : GL (Fin 4) F where
  val := LinearMap.toMatrix' (pointTransvection J w)
  inv := LinearMap.toMatrix' (pointTransvection J w)
  val_inv := by
    rw [← LinearMap.toMatrix'_mul]
    have ht : pointTransvection J w * pointTransvection J w = 1 := by
      apply LinearMap.ext
      exact pointTransvection_involutive J w hw
    rw [ht, LinearMap.toMatrix'_one]
  inv_val := by
    rw [← LinearMap.toMatrix'_mul]
    have ht : pointTransvection J w * pointTransvection J w = 1 := by
      apply LinearMap.ext
      exact pointTransvection_involutive J w hw
    rw [ht, LinearMap.toMatrix'_one]

private lemma pointTransvectionGL_apply (J : HermitianForm 4 F) (w : V)
    (hw : pairing J w w = 0) (x : V) :
    (pointTransvectionGL J w hw).val *ᵥ x = pointTransvection J w x :=
  LinearMap.toMatrix'_mulVec _ _

omit [CharP F 2] in
private lemma gram_entry (J : HermitianForm 4 F) (A : Matrix (Fin 4) (Fin 4) F)
    (i j : Fin 4) :
    (J.conjTranspose A * J.form * A) i j =
      pairing J (A *ᵥ Pi.single i 1) (A *ᵥ Pi.single j 1) := by
  simp only [mulVec_single_one]
  simp only [pairing, dotProduct, mulVec, mul_apply,
    HermitianForm.conjTranspose, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  simp only [Matrix.col, Matrix.transpose_apply]
  ring

private lemma pointTransvectionGL_mem (J : HermitianForm 4 F) (w : V)
    (hw : pairing J w w = 0) : pointTransvectionGL J w hw ∈ J.unitarySubgroup := by
  rw [J.mem_unitarySubgroup_iff]
  ext i j
  rw [gram_entry, pointTransvectionGL_apply, pointTransvectionGL_apply,
    pointTransvection_isometry J w hw]
  simp [pairing, dotProduct, Pi.single_apply, apply_ite]

private lemma point_transport_of_pairing_ne_zero (J : HermitianForm 4 F) (u v : V)
    (hu : pairing J u u = 0) (hv : pairing J v v = 0)
    (huv : pairing J u v ≠ 0) :
    ∃ (A : GL (Fin 4) F) (c : F), A ∈ J.unitarySubgroup ∧ c ≠ 0 ∧
      A.val *ᵥ u = c • v := by
  let c := (pairing J u v)⁻¹
  let z := c • v
  have hc : c ≠ 0 := inv_ne_zero huv
  have hz : pairing J z z = 0 := by
    simp only [z, pairing_smul_left, pairing_smul_right, hv, mul_zero]
  have huz : pairing J u z = 1 := by
    simpa only [z, c, pairing_smul_right] using inv_mul_cancel₀ huv
  have hzu : pairing J z u = 1 := by
    rw [← pairing_conj, huz, map_one]
  have hw : pairing J (u + z) (u + z) = 0 := by
    simp only [pairing_add_left, pairing_add_right, hu, hz, huz, hzu,
      zero_add, add_zero, CharTwo.add_self_eq_zero]
  refine ⟨pointTransvectionGL J (u + z) hw, c, pointTransvectionGL_mem J _ hw, hc, ?_⟩
  rw [pointTransvectionGL_apply, pointTransvection_apply, pairing_add_left, hu, hzu,
    zero_add, one_smul]
  ext i
  change u i + (u i + z i) = z i
  rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

omit [CharP F 2] in
private lemma standard_pairing (σ : F ≃+* F) (hσ : Function.Involutive σ) (x y : V) :
    pairing (UnitaryFourFlag.form F σ hσ) x y =
      σ (x 0) * y 3 + σ (x 1) * y 2 + σ (x 2) * y 1 + σ (x 3) * y 0 := by
  simp [pairing, UnitaryFourFlag.form, UnitaryFourFlag.gram, mulVec, dotProduct,
    Fin.sum_univ_succ]
  ring

private lemma exists_point_vector_transport (σ : F ≃+* F) (hσ : Function.Involutive σ)
    (v : V) (hv0 : v ≠ 0) (hv : pairing (UnitaryFourFlag.form F σ hσ) v v = 0) :
    ∃ (A : GL (Fin 4) F) (c : F), A ∈ (UnitaryFourFlag.form F σ hσ).unitarySubgroup ∧
      c ≠ 0 ∧ A.val *ᵥ ![1, 0, 0, 0] = c • v := by
  let J := UnitaryFourFlag.form F σ hσ
  let u : V := ![1, 0, 0, 0]
  have hu : pairing J u u = 0 := by simp [J, u, standard_pairing]
  by_cases hv3 : v 3 = 0
  · have hz : ∃ z : V, pairing J z z = 0 ∧ pairing J u z ≠ 0 ∧ pairing J z v ≠ 0 := by
      by_cases hvfirst : v 0 = 0
      · by_cases hvsecond : v 1 = 0
        · have hvthird : v 2 ≠ 0 := by
            intro h
            apply hv0
            ext i
            fin_cases i <;> simp_all
          refine ⟨![0, 1, 0, 1], ?_, ?_, ?_⟩ <;>
            simp [J, u, standard_pairing, hvfirst, hvthird]
        · refine ⟨![0, 0, 1, 1], ?_, ?_, ?_⟩ <;>
            simp [J, u, standard_pairing, hvfirst, hvsecond]
      · refine ⟨![0, 0, 0, 1], ?_, ?_, ?_⟩ <;>
          simp [J, u, standard_pairing, hvfirst]
    obtain ⟨z, hzz, huz, hzv⟩ := hz
    obtain ⟨A, a, hA, ha, hAu⟩ := point_transport_of_pairing_ne_zero J u z hu hzz huz
    obtain ⟨B, b, hB, hb, hBz⟩ := point_transport_of_pairing_ne_zero J z v hzz hv hzv
    refine ⟨B * A, a * b, J.unitarySubgroup.mul_mem hB hA, mul_ne_zero ha hb, ?_⟩
    change (B.val * A.val) *ᵥ u = (a * b) • v
    rw [← mulVec_mulVec, hAu, mulVec_smul, hBz, smul_smul]
  · exact point_transport_of_pairing_ne_zero J u v hu hv (by
      simpa [J, u, standard_pairing] using hv3)

/-- Every isotropic line in the antidiagonal Hermitian four-space is the image
of the coordinate point under an actual unitary matrix, including `n = 1`. -/
public theorem exists_point_unitary_transport [Finite F]
    (σ : F ≃+* F) (hσ : Function.Involutive σ)
    (n : ℕ) (_hn : 0 < n) (_hcard : Nat.card F = (2 ^ n) ^ 2)
    (_hconj : ∀ x, σ x = x ^ (2 ^ n))
    (W : Submodule F V) (hd : Module.finrank F W = 1)
    (hi : W ≤ orthogonal (UnitaryFourFlag.form F σ hσ) W) :
    ∃ A : GL (Fin 4) F, A ∈ (UnitaryFourFlag.form F σ hσ).unitarySubgroup ∧
      W = (UnitaryFourFlag.pointSpace F).map A.val.mulVecLin := by
  classical
  have hW : W ≠ ⊥ := by
    intro h
    rw [h] at hd
    simp at hd
  obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hvv : pairing (UnitaryFourFlag.form F σ hσ) v v = 0 := hi hvW v hvW
  obtain ⟨A, c, hA, hc, hAv⟩ := exists_point_vector_transport σ hσ v hv0 hvv
  refine ⟨A, hA, ?_⟩
  have hp : UnitaryFourFlag.pointSpace F = Submodule.span F {![1, 0, 0, 0]} := by
    apply le_antisymm
    · intro x hx
      have hx' : x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 := hx
      have he : x = x 0 • ![1, 0, 0, 0] := by
        ext i
        fin_cases i <;> simp [hx'.1, hx'.2.1, hx'.2.2]
      rw [he]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · apply Submodule.span_le.mpr
      intro x hx
      obtain rfl : x = ![1, 0, 0, 0] := Set.mem_singleton_iff.mp hx
      change (![1, 0, 0, 0] : V) 1 = 0 ∧ _
      simp
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hd hvW hv0, hp, Submodule.map_span]
  simp only [Set.image_singleton]
  change Submodule.span F {v} = Submodule.span F {A.val *ᵥ ![1, 0, 0, 0]}
  rw [hAv, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc)]

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.TwoLocalCover
