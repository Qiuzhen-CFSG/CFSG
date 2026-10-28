module

public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Section kernels and normalizers of covering subgroups

The intrinsic two-core of a C-component lies in the ambient two-core.
A covering subgroup therefore has the same image as the component in that
quotient. Uniqueness of component lifting reflects its normalizer. The same
argument turns commutation modulo the ambient two-core into normalization
and commutation modulo the component's intrinsic two-core.

These finite-group deductions supply the normalizer comparison used in the
nonnormal case of Aschbacher–Smith, 4.2.12 and 4.4.5–6 (combined manuscript,
1 March 2004, printed pp.609 and 620).
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
/-- A cover of a C-component modulo its two-core has no larger normalizer. -/
theorem normalizer_cover_le_component_normalizer {K A : Subgroup G}
    (hK : K.IsCComponent) (hAK : A ≤ K)
    (hcover : (K : Set G) ⊆ (A : Set G) * (K.pCoreIn 2 : Set G)) :
    normalizer (A : Set G) ≤ normalizer (K : Set G) := by
  let N := pCore 2 G
  let q := QuotientGroup.mk' N
  let : Group.IsNilpotent N := pCore_isPGroup.isNilpotent
  have hqA : A.map q = K.map q := by
    apply le_antisymm (map_mono hAK)
    rintro _ ⟨k,hk,rfl⟩
    obtain ⟨a,ha,c,hc,he⟩ := hcover hk
    refine ⟨a,ha,?_⟩
    rw [←he,map_mul]
    have hz : q c = 1 := (QuotientGroup.eq_one_iff c).mpr
      (pCoreIn_le_of_subnormal 2 hK.subnormal hc)
    simp only [hz,mul_one]
  rw [← normalizer_cComponent_quotient hK N,←hqA]
  exact map_le_iff_le_comap.mp (le_normalizer_map q)

/-- An actor centralizing a C-component modulo the ambient two-core already
normalizes it and centralizes its intrinsic two-core quotient. -/
theorem section_kernel_controls_cComponent {K B : Subgroup G}
    (hK : K.IsCComponent) (hcomm : ⁅B,K⁆ ≤ pCore 2 G) :
    B ≤ normalizer (K : Set G) ∧ ⁅B,K⁆ ≤ K.pCoreIn 2 := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
  have hc : ⁅B.map q,K.map q⁆ = ⊥ := by
    rw [←map_commutator,map_eq_bot_iff,QuotientGroup.ker_mk']
    exact hcomm
  have hn : B ≤ normalizer (K : Set G) := by
    rw [←normalizer_cComponent_quotient hK (pCore 2 G)]
    exact map_le_iff_le_comap.mp
      ((commutator_eq_bot_iff_le_centralizer.mp hc).trans (centralizer_le_normalizer _))
  refine ⟨hn,?_⟩
  have hm : ⁅B,K⁆ ≤ K := le_normalizer_iff_commutator_le_right.mp hn
  intro x hx
  change x ∈ (pCore 2 K).map K.subtype
  rw [pCore_subnormal_eq_comap 2 hK.subnormal]
  exact ⟨⟨x,hm hx⟩,hcomm hx,rfl⟩
end Subgroup
