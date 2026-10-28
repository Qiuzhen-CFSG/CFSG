module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.ChiefFlag.Spaces
public import Theory.Mathieu.M22.Properties.FixedHexadLocal.RepresentativeKernel.Enumeration
public import Theory.Mathieu.M22.Properties.FixedHexadLocal.Fusion
public import Mathlib.GroupTheory.Sylow

/-!
# A native cubic actor centralizing a hexad-kernel involution

The checked native M22 involution centralizer has order 384. Cauchy's theorem
and the checked fusion theorem give a commuting cubic for every involution.
An element of the marked kernel fixes the source octad pointwise and therefore
lifts to native M22. Its native fixed hexad augments to precisely that octad,
so its commuting cubic lies in the required hexad stabilizer. All embedding
and lift equations are retained for the independent code-displacement input.

Source: Aschbacher--Smith, H.14.4(2) and H.16.4(5), printed pp.397--398,403.
-/

public section
noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open scoped Pointwise
namespace MathieuCode.Hexad.ChiefFlag.FixedQuotientNative
open Subgroup

/-- Cauchy in the checked order-384 centralizer, transported through native
involution fusion. No point-count or centralizer-order premise is assumed. -/
theorem native_commuting_cubic (z : M22) (hz : orderOf z = 2) :
    ∃ y : M22, orderOf y = 3 ∧ Commute y z := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := M22RepresentativeKernel.C) 3
    (by rw [M22RepresentativeKernel.centralizer_card]; decide)
  obtain ⟨g, hg⟩ := isConj_iff.mp
    (m22_involutions_isConj m22GeneratorAInM22 z M22RepresentativeKernel.representative_order hz)
  refine ⟨MulAut.conj g y.val, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hy]
  · have hc0 : Commute y.val m22GeneratorAInM22 :=
      Subgroup.mem_centralizer_singleton_iff.mp y.property
    have hc := hc0.map (MulAut.conj g)
    change Commute (MulAut.conj g y.val) (g * m22GeneratorAInM22 * g⁻¹) at hc
    rwa [hg] at hc

private theorem coordinates_cover (i : Fin 24) :
    i = 0 ∨ i = 9 ∨ ∃ j : Fin 22, m22Coordinates j = i := by
  revert i
  decide +kernel

/-- The actual source octad equals the augmented fixed hexad of its lifted
nonidentity kernel involution. -/
theorem sourceOctad_eq_fixed_hexad (h : OuterRestrictionInput m22SourceOctad)
    (z : Kernel) (u : M22) (hu : m22Embedding u = z.val.val) (hu2 : orderOf u = 2) :
    m22SourceOctad.val = m22AugmentedOctad (m22FixedPoints u) := by
  have hz : z.val.val ∈ octadPointwiseKernel m22SourceOctad := by
    rw [← h.kernel_image]
    exact ⟨z.val, z.property, rfl⟩
  have hf := (mem_octadPointwiseKernel _ _).mp hz
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    apply (mem_m22AugmentedOctad _ _).mpr
    rcases coordinates_cover i with rfl | rfl | ⟨j, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · refine Or.inr (Or.inr ⟨j, ?_, rfl⟩)
      apply (mem_m22FixedPoints u j).mpr
      apply m22Coordinates.injective
      rw [← m22Embedding_apply, hu]
      exact hf _ hi
  · rw [m24Blocks_card _ m22SourceOctad.property,
      m24Blocks_card _ (m22AugmentedOctad_mem (m22FixedPoints_mem_blocks u hu2))]

/-- The cubic belongs to the actual outer hexad stabilizer, and retains its
native M22 lift for the independently supplied displacement bound. -/
theorem commuting_cubic (h : OuterRestrictionInput m22SourceOctad)
    (z : Kernel) (hz : orderOf z = 2) :
    ∃ (y : Stabilizer) (u : M22), orderOf y = 3 ∧ orderOf u = 3 ∧
      m22ToPairStabilizer u = y.val ∧ Commute y.val z.val := by
  have hzO : z.val.val ∈ octadPointwiseKernel m22SourceOctad := by
    rw [← h.kernel_image]
    exact ⟨z.val, z.property, rfl⟩
  have hf := (mem_octadPointwiseKernel _ _).mp hzO
  have hr : z.val.val ∈ m22Embedding.range := by
    rw [m22Embedding_range]
    exact ⟨hf 0 (by decide +kernel), hf 9 (by decide +kernel)⟩
  obtain ⟨t, ht⟩ := hr
  have ht2 : orderOf t = 2 := by
    rw [← orderOf_injective m22Embedding m22Embedding_injective, ht,
      Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  obtain ⟨u, hu, hut⟩ := native_commuting_cubic t ht2
  have he := sourceOctad_eq_fixed_hexad h z t ht ht2
  have hus : u • m22FixedPoints t = m22FixedPoints t :=
    m22_centralizer_le_fixedPoints_stabilizer t
      (Subgroup.mem_centralizer_singleton_iff.mpr hut)
  have hy : m22ToPairStabilizer u ∈ Stabilizer := by
    change m22Embedding u • m22SourceOctad.val = m22SourceOctad.val
    rw [he, ← m22AugmentedOctad_smul, hus]
  let y : Stabilizer := ⟨m22ToPairStabilizer u, hy⟩
  have hi : Function.Injective m22ToPairStabilizer := by
    intro a b hab
    exact m22Embedding_injective (congrArg Subtype.val hab)
  refine ⟨y, u, ?_, hu, rfl, ?_⟩
  · rw [← Subgroup.orderOf_coe y]
    exact (orderOf_injective m22ToPairStabilizer hi u).trans hu
  · have hc := hut.map m22Embedding
    rw [ht] at hc
    apply Commute.of_map (f := m22PairStabilizer.subtype) Subtype.val_injective
    exact hc

end MathieuCode.Hexad.ChiefFlag.FixedQuotientNative
