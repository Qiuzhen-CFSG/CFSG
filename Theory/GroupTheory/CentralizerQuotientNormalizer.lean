module
public import Theory.GroupAction.QuotientConjugation
public import Mathlib.GroupTheory.Commutator.Basic
/-!
# Quotient normalizers preserve the original commutator module

Adjoining C_G(V) to K leaves [V,K] unchanged. Hence a normalizer of the
image of K in G/C_G(V) lifts to a normalizer of the original [V,K].
No central layer is removed from V or its commutator subgroup.
Source application: Aschbacher–Smith C.5.13, printed pp.162–163.
-/
public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G]
theorem commutator_sup_centralizer_eq (V K : Subgroup G) [V.Normal] :
    ⁅V,K ⊔ centralizer (V : Set G)⁆ = ⁅V,K⁆ := by
  apply le_antisymm
  · apply commutator_le.mpr
    intro v hv t ht
    obtain ⟨k,hk,c,hc,rfl⟩ := mem_sup_of_normal_right.mp ht
    have he : ⁅v,c⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hc v hv)
    simpa only [commutatorElement_mul_right_eq_mul_conj,he,mul_one,mul_inv_cancel_right]
      using commutator_mem_commutator hv hk
  · exact commutator_mono le_rfl le_sup_left

theorem normalizer_centralizerQuotient_image_le (V K : Subgroup G) [V.Normal] :
    let q := QuotientGroup.mk' (centralizer (V : Set G))
    (normalizer (K.map q : Set _)).comap q ≤ normalizer (⁅V,K⁆ : Subgroup G) := by
  let q := QuotientGroup.mk' (centralizer (V : Set G))
  change (normalizer (K.map q : Set _)).comap q ≤ normalizer (⁅V,K⁆ : Subgroup G)
  rw [comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective _),
    comap_map_eq,QuotientGroup.ker_mk']
  intro g hg
  rw [← commutator_sup_centralizer_eq V K]
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp hg,
    mem_normalizer_iff_map_conj_eq.mp (show g ∈ normalizer (V : Set G) from
      (normalizer_eq_top V ▸ mem_top g))]

end Subgroup
