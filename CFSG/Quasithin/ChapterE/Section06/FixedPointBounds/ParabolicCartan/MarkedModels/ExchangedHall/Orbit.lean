module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source
public import Theory.GroupTheory.PCoreAbelianQuotient
public import Theory.GroupTheory.ComponentLocalOrbitAbelian
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# The normal Borel orbit in the exchanged branch

The source product M = B B^(t) S implies M = ⟨B,S⟩, retaining the
right-conjugation convention B^(t) = t⁻¹ B t. The S-conjugates of B
generate a subgroup N normal in M. In X/J, the supplied quasisimple
two-core quotient makes the component image an ordinary component.
Its stabilizer preserves the actual overlap M* ∩ K*. Consequently two
conjugate overlaps coincide or commute. Their derived subgroups lie
in the orbit of the seed two-core, hence in O₂(M*).

The equality J = O₂(X) lifts this to [N,N] ≤ O₂(M). Relative normality,
the overlap identity and the core-image comparison are proved for the
literal maps. There is no assumption that K itself is normal in X.

Source: Aschbacher--Smith, E.2.2(1), pp.215--216, and 4.4.13,
pp.623--624; the component calculus is A.3.3.
-/

public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.ExchangedHall
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The exact exchanged-product equality implies generation by the overlap and the original actor. -/
theorem exchanged_join {M K T : Subgroup G} (hc : ExchangedClauses M K T)
    (hTM : T ≤ M) : (M ⊓ K) ⊔ T = M := by
  obtain ⟨t, ht, _, hprod⟩ := hc.exchanged_product
  apply le_antisymm (sup_le inf_le_left hTM)
  have hconj : (M ⊓ K).conjBy t⁻¹ ≤ (M ⊓ K) ⊔ T := by
    rintro x ⟨b, hb, rfl⟩
    exact ((M ⊓ K) ⊔ T).mul_mem
      (((M ⊓ K) ⊔ T).mul_mem (mem_sup_right (T.inv_mem ht)) (mem_sup_left hb))
      (mem_sup_right (by simpa using ht))
  intro x hx
  change x ∈ (M : Set G) at hx
  rw [hprod] at hx
  obtain ⟨y, ⟨b, hb, c, hc, rfl⟩, t, ht, rfl⟩ := hx
  exact ((M ⊓ K) ⊔ T).mul_mem
    (((M ⊓ K) ⊔ T).mul_mem (mem_sup_left hb) (hconj hc)) (mem_sup_right ht)

omit [Finite G] in
/-- The normal core lies in M, so the image of the overlap is the overlap of the actual images. -/
theorem source_overlap_eq (M K : Subgroup G) :
    sourceImage M (M ⊓ K) = sourceImage M M ⊓ sourceImage M K := by
  let q := QuotientGroup.mk' (sourceKernel M)
  have hpre : (M.map q).comap q = M := by
    rw [comap_map_eq, QuotientGroup.ker_mk']
    exact sup_eq_left.mpr M.normalCore_le
  apply le_antisymm (map_inf_le M K q)
  rintro x ⟨hxM, y, hyK, rfl⟩
  have hyM : y ∈ M := by
    rw [← hpre]
    exact hxM
  exact ⟨y, ⟨hyM, hyK⟩, rfl⟩

omit [Finite G] in
/-- Only the component stabilizer in the actor is required to normalize the marked overlap. -/
theorem source_overlap_invariant {M K T : Subgroup G} (hTM : T ≤ M) :
    sourceImage M T ⊓ normalizer (sourceImage M K : Set _) ≤
      normalizer (sourceImage M (M ⊓ K) : Set _) := by
  rw [source_overlap_eq]
  exact (le_inf ((inf_le_left.trans (map_mono hTM)).trans
    (sourceImage M M).le_normalizer) inf_le_right).trans
      inf_normalizer_le_normalizer_inf

/-- The component image in X/J is quasisimple via the exact intrinsic two-core kernel. -/
theorem source_component {M K T : Subgroup G} (hc : ExchangedClauses M K T)
    (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K)) :
    IsComponent (G ⧸ sourceKernel M) (sourceImage M K) := by
  refine ⟨hK.subnormal.map (QuotientGroup.mk'_surjective _), ?_⟩
  let := hq
  let f := (QuotientGroup.mk' (sourceKernel M)).subgroupMap K
  have he : f.ker = pCore 2 K := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk', hc.kernel_eq]
    exact (pCore_subnormal_eq_comap 2 hK.subnormal).symm
  exact IsQuasisimple.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq he.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f
        ((QuotientGroup.mk' (sourceKernel M)).subgroupMap_surjective K)))

/-- Construct a subgroup normal in M with a two-subgroup supplement and derived subgroup in O₂(M). -/
theorem normal_section {M K T : Subgroup G} (hc : ExchangedClauses M K T)
    (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hTM : T ≤ M)
    (hd : ⁅sourceImage M (M ⊓ K), sourceImage M (M ⊓ K)⁆ ≤
      (sourceImage M (M ⊓ K)).pCoreIn 2) :
    ∃ N : Subgroup G, N ≤ M ∧ M ≤ normalizer (N : Set G) ∧
      N ⊔ T = M ∧ ⁅N, N⁆ ≤ M.pCoreIn 2 := by
  let B := M ⊓ K
  let N := componentOrbit B T
  let q := QuotientGroup.mk' (sourceKernel M)
  have hgen : B ⊔ T = M := exchanged_join hc hTM
  have hNM : N ≤ M := (componentOrbit_le_sup B T).trans hgen.le
  have hn : M ≤ normalizer (N : Set G) := by
    rw [← hgen]
    exact (normal_subgroupOf_iff_le_normalizer (componentOrbit_le_sup B T)).mp
      (componentOrbit_normal_subgroupOf_sup B T)
  refine ⟨N, hNM, hn, (componentOrbit_sup B T).trans hgen, ?_⟩
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk', hc.kernel_eq]
    exact pCore_isPGroup
  have hmap := (source_component hc hK hq).local_orbit_commutator_le_pCoreIn
    (map_mono (f := q) inf_le_right) (source_overlap_invariant hTM) hd
  have hm : B.map q ⊔ T.map q = M.map q := by rw [← Subgroup.map_sup, hgen]
  change ⁅componentOrbit (B.map q) (T.map q), componentOrbit (B.map q) (T.map q)⁆ ≤
    (B.map q ⊔ T.map q).pCoreIn 2 at hmap
  rw [hm, ← map_componentOrbit, ← map_commutator,
    ← map_pCoreIn_of_ker_isPGroup q hk] at hmap
  have hle := map_le_iff_le_comap.mp hmap
  rw [comap_map_eq] at hle
  have hkM : q.ker ≤ M.pCoreIn 2 := by
    apply le_pCoreIn_of_normalizes hk
    · rw [QuotientGroup.ker_mk']
      exact M.normalCore_le
    · rw [normalizer_eq_top]
      exact le_top
  simpa only [sup_eq_left.mpr hkM] using hle

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.ExchangedHall
