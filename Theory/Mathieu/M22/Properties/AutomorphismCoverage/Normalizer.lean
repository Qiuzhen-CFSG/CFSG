module

public import Theory.Mathieu.M22.Properties.FixedHexads
public import Theory.Mathieu.M22.Properties.HexadExtension

/-!
# Recovering the hexad design from the permutation group M₂₂

The checked involution geometry identifies involution fixed-point sets with
hexads. Transitivity on hexads supplies the converse: every hexad is such a
fixed-point set. Conjugation by a permutation normalizing M₂₂ preserves orders
and transports fixed-point sets, so it preserves the entire design.

This proves the geometric normalizer step for GLS3, Table 5.3c, Note 1.
The involution geometry is imported from the concrete M₂₂/M₂₃ models;
no assertion about the abstract automorphism group is used.
-/

open MulAction
open scoped Pointwise
namespace Sporadic.Mathieu

private theorem normalizer_fixedPoints
    (σ : Subgroup.normalizer (M22 : Set (Equiv.Perm (Fin 22)))) (t : M22) :
    m22FixedPoints (M22.normalizerMonoidHom σ t) =
      (σ : Equiv.Perm (Fin 22)) • m22FixedPoints t := by
  ext x
  rw [mem_m22FixedPoints, Finset.mem_smul_finset]
  change σ.val (t.val (σ.val⁻¹ x)) = x ↔ _
  constructor
  · intro hx
    refine ⟨σ.val⁻¹ x, (mem_m22FixedPoints t _).mpr ?_, ?_⟩
    · change t.val (σ.val⁻¹ x) = σ.val⁻¹ x
      exact σ.val.injective (hx.trans (Equiv.apply_symm_apply σ.val x).symm)
    · exact Equiv.apply_symm_apply σ.val x
  · rintro ⟨y, hy, rfl⟩
    have hty := (mem_m22FixedPoints t y).mp hy
    change t.val y = y at hty
    simp only [Equiv.Perm.smul_def,
      show σ.val⁻¹ (σ.val y) = y from σ.val.symm_apply_apply y, hty]

/-- Every hexad is the full fixed-point set of an involution of M₂₂. -/
public theorem m22_hexad_eq_fixedPoints_involution (B : Finset (Fin 22)) (hB : B ∈ m22Blocks) :
    ∃ t : M22, orderOf t = 2 ∧ m22FixedPoints t = B := by
  let t₀ := m22GeneratorAInM22
  have ht₀ : orderOf t₀ = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact m22GeneratorA_order
  obtain ⟨g, hg⟩ := exists_smul_m22Hexad123_eq hB
  obtain ⟨g₀, hg₀⟩ := exists_smul_m22Hexad123_eq (m22FixedPoints_mem_blocks t₀ ht₀)
  let k : Subgroup.normalizer (M22 : Set (Equiv.Perm (Fin 22))) :=
    ⟨(g * g₀⁻¹).val, Subgroup.le_normalizer (g * g₀⁻¹).property⟩
  refine ⟨M22.normalizerMonoidHom k t₀,
    ((M22.normalizerMonoidHom k).orderOf_eq t₀).trans ht₀, ?_⟩
  rw [normalizer_fixedPoints]
  change (g * g₀⁻¹) • m22FixedPoints t₀ = B
  rw [← hg₀, mul_smul, inv_smul_smul, hg]

private theorem normalizer_mem_designAut
    (σ : Subgroup.normalizer (M22 : Set (Equiv.Perm (Fin 22)))) :
    σ.val ∈ m22DesignAut := by
  have hp (τ : Subgroup.normalizer (M22 : Set (Equiv.Perm (Fin 22))))
      (B : Finset (Fin 22)) (hB : B ∈ m22Blocks) :
      τ.val • B ∈ m22Blocks := by
    obtain ⟨t, ht, rfl⟩ := m22_hexad_eq_fixedPoints_involution B hB
    rw [← normalizer_fixedPoints]
    exact m22FixedPoints_mem_blocks _ (((M22.normalizerMonoidHom τ).orderOf_eq t).trans ht)
  rw [m22DesignAut, Theory.GroupTheory.SteinerSystem.mem_aut_iff]
  change σ.val • (m22Blocks : Set (Finset (Fin 22))) = _
  apply Set.Subset.antisymm
  · rintro B ⟨C, hC, rfl⟩
    exact hp σ C hC
  · intro B hB
    exact ⟨σ.val⁻¹ • B, hp σ⁻¹ B hB, smul_inv_smul σ.val B⟩

/-- Every permutation normalizing the concrete M₂₂ preserves the hexad design. -/
public theorem m22_normalizer_le_designAut :
    Subgroup.normalizer (M22 : Set (Equiv.Perm (Fin 22))) ≤ m22DesignAut := by
  intro σ hσ
  exact normalizer_mem_designAut ⟨σ, hσ⟩

end Sporadic.Mathieu
