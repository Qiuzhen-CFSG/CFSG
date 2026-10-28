module

public import Theory.Representation.HermitianTensorThree.ImageOuter.Normalizer.Contracts
/-!
# Fixed-field semilinearity from the scalar centralizer

A binary normalizer conjugates the group of fixed-field scalar maps to
itself. Applying the conjugated scalar operators to one marked coordinate
recovers an additive and multiplicative map of the actual fixed field.
It is an automorphism because the field is finite. The resulting scalar
identity proves semilinearity on the literal descended Hermitian space.
Only the explicitly supplied scalar-centralizer contract is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.4.2 setup,
printed p.380. This is the coefficient-recovery step in the normalizer proof.
-/

public section
noncomputable section
namespace Representation.HermitianTensorThree.ImageOuter
variable (n : ℕ) [NeZero n]

private theorem fixedScalar_commutes (c : (F n)ˣ) (a : Cover n) :
    fixedScalar n c * binaryActionHom n a = binaryActionHom n a * fixedScalar n c := by
  apply LinearEquiv.ext
  intro X
  exact ((actionHom n a).map_smul c.val X).symm

private theorem normalizer_conjugate_scalar (hcentral : ScalarCentralizerCoverage n)
    (e : Space n ≃ₗ[ZMod 2] Space n) (he : e ∈ binaryNormalizer n) (c : (F n)ˣ) :
    ∃ d : (F n)ˣ, e * fixedScalar n c * e⁻¹ = fixedScalar n d := by
  apply hcentral
  intro a
  obtain ⟨b, hb⟩ := (Subgroup.mem_normalizer_iff''.mp he (binaryActionHom n a)).mp ⟨a, rfl⟩
  have h := congrArg (fun x => e * x * e⁻¹) (fixedScalar_commutes n c b)
  rw [hb] at h
  simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left,
    mul_inv_cancel_right, inv_mul_cancel_right, mul_inv_cancel, mul_one] using h

/-- A normalizer acts semilinearly over the actual fixed field. -/
theorem normalizer_semilinear_of_scalarCentralizer (hcentral : ScalarCentralizerCoverage n)
    (e : Space n ≃ₗ[ZMod 2] Space n) (he : e ∈ binaryNormalizer n) :
    ∃ τ : F n ≃+* F n, ∀ (c : F n) (X : Space n), e (c • X) = τ c • e X := by
  let q (c : F n) : Space n →+ Space n := {
    toFun := fun X => e (c • e.symm X)
    map_zero' := by simp
    map_add' := by intro X Y; simp [smul_add] }
  have hq (c : F n) : ∃ d : F n, ∀ X, q c X = d • X := by
    by_cases hc : c = 0
    · exact ⟨0, fun X => by simp [q, hc]⟩
    · obtain ⟨d, hd⟩ := normalizer_conjugate_scalar n hcentral e he (Units.mk0 c hc)
      refine ⟨d.val, fun X => ?_⟩
      exact congrArg (fun f : Space n ≃ₗ[ZMod 2] Space n => f X) hd
  let v : Space n := (coordinates n).symm (Pi.single 0 1, 0)
  let φ : F n → F n := fun c => ((coordinates n) (q c v)).1 0
  have hv : ((coordinates n) v).1 0 = 1 := by simp [v]
  have hφ (c : F n) (X : Space n) : q c X = φ c • X := by
    obtain ⟨d, hd⟩ := hq c
    have hh : φ c = d := by simp [φ, hd, hv]
    exact hh ▸ hd X
  have hmul (a b : F n) (X : Space n) : q (a * b) X = q a (q b X) := by
    simp [q, mul_smul]
  let φhom : F n →+* F n := {
    toFun := φ
    map_one' := by simpa [φ, q] using hv
    map_mul' := by
      intro a b
      change ((coordinates n) (q (a * b) v)).1 0 = φ a * φ b
      rw [hmul, hφ, hφ]
      simp [hv]
    map_zero' := by simp [φ, q]
    map_add' := by intro a b; simp [φ, q, add_smul] }
  refine ⟨RingEquiv.ofBijective φhom
    ⟨φhom.injective, Finite.surjective_of_injective φhom.injective⟩, fun c X => ?_⟩
  have h := hφ c (e X)
  change e (c • X) = φ c • e X
  simpa only [q, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearEquiv.symm_apply_apply] using h

end Representation.HermitianTensorThree.ImageOuter
