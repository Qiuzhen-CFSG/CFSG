module

public import Theory.Representation.HermitianTensorThree.ImageOuter.Normalizer
public import Theory.Representation.HermitianTensorThree.ImageOuter.OuterRank

/-!
# Fixed-field linear conjugacy for outer Hermitian involutions

A normalizer conjugator is a GL₃ congruence followed by a coefficient
map. The coefficient map commutes with the marked quadratic involution.
Removing it on the left therefore preserves the conjugacy and leaves an
F-linear congruence. This permits transport of the literal F-linear sections.

Source: Aschbacher–Smith, H.4.4(6), printed p.381.
-/

public section
noncomputable section
namespace Representation.HermitianTensorThree.ImageOuter.OuterInvolutions
open Representation.HermitianTensorThree.ImageOuter
variable (n : ℕ) [NeZero n]

theorem coefficient_commutes_swap (τ : E n ≃+* E n) :
    coefficient n τ * fieldSwapBinary n = fieldSwapBinary n * coefficient n τ := by
  apply LinearEquiv.ext
  intro X
  apply Subtype.ext
  change ((fieldSwap n X).val).map τ = (fieldSwap n (coefficient n τ X)).val
  rw [fieldSwap_eq_map, fieldSwap_eq_map, coefficient_apply]
  ext j k
  exact (sigma_map n τ (X.val j k)).symm

/-- The conjugator can preserve the actual fixed field, even though the full
normalizer also contains coefficient automorphisms. -/
theorem exists_linear_conjugator
    (i : Space n ≃ₗ[ZMod 2] Space n) (hiN : i ∈ binaryNormalizer n)
    (hi2 : orderOf i = 2) (hiL : i ∉ binaryImage n) :
    ∃ c : Space n ≃ₗ[F n] Space n, binaryEquiv n c ∈ binaryNormalizer n ∧
      MulAut.conj (binaryEquiv n c) i = fieldSwapBinary n := by
  obtain ⟨b, hb, hbi⟩ := OuterRank.outer_involution_conjugate n (normalizerCoverage n) i hiN hi2 hiL
  obtain ⟨g, τ, hbg⟩ := normalizerCoverage n b hb
  let k := Matrix.GeneralLinearGroup.map τ.symm.toRingHom g
  have hk : binaryCongruence n k = (coefficient n τ)⁻¹ * b := by
    apply LinearEquiv.ext
    intro X
    apply Subtype.ext
    change k.val * X.val * adjoint n k.val = (b X).val.map τ.symm
    rw [hbg, Matrix.map_mul, Matrix.map_mul, ← adjoint_map]
    congr 2
    ext j l
    exact (τ.symm_apply_apply _).symm
  refine ⟨congruence n k, binaryCongruence_mem_normalizer n k, ?_⟩
  change MulAut.conj (binaryCongruence n k) i = _
  rw [hk, MulAut.conj_apply, mul_inv_rev, inv_inv]
  calc
    _ = (coefficient n τ)⁻¹ * (b * i * b⁻¹) * coefficient n τ := by group
    _ = (coefficient n τ)⁻¹ * fieldSwapBinary n * coefficient n τ := by rw [← MulAut.conj_apply, hbi]
    _ = fieldSwapBinary n := by
      rw [mul_assoc, ← coefficient_commutes_swap, inv_mul_cancel_left]
end Representation.HermitianTensorThree.ImageOuter.OuterInvolutions
