module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ActionGeneration
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.LocalTransfer

/-!
# Lifting factors and their commutators from the star quotient

The intrinsic two-core of a relatively subnormal subgroup is its intersection
with the ambient two-core. A full inverse image inside an invariant subgroup
inherits normalization from its star image: the difference between a conjugate
and a chosen lift lies in the specified kernel. Once normalization is known,
commutation of the star images puts the actual commutator in the intrinsic
two-core. No ambient normality of H or L is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49(i), printed pp.1143–1144.
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration
variable {G : Type*} [Group G]

theorem localTwoCore_eq_intersection [Finite G]
    (H L : Subgroup G) (hLH : L ≤ H) (hsub : (L.subgroupOf H).IsSubnormal) :
    localTwoCore L = L ⊓ localTwoCore H := by
  exact le_antisymm (le_inf (map_subtype_le _)
    (pCoreAmbient_mono_of_isSubnormalIn L H 2 hLH hsub))
    (inf_pCoreIn_le_of_le 2 hLH)

/-- A full inverse image inside an invariant subgroup inherits normalization
from its star image. The kernel condition specifies the canonical lift. -/
theorem normalizes_saturated_of_star_normalizes
    (H J L Y0 : Subgroup G) (hLH : L ≤ H) (hYH : Y0 ≤ H)
    (hLJ : L ≤ J) (hkernel : J ⊓ localTwoCore H ≤ L)
    (hJ : Y0 ≤ normalizer (J : Set G))
    (hstar : starImage H Y0 ≤ normalizer (starImage H L : Set (H ⧸ pCore 2 H))) :
    Y0 ≤ normalizer (L : Set G) := by
  apply le_normalizer_iff.mpr
  intro y hy l hl
  let q := QuotientGroup.mk' (pCore 2 H)
  let yH : H := ⟨y, hYH hy⟩
  let lH : H := ⟨l, hLH hl⟩
  let c : H := yH * lH * yH⁻¹
  have hc : q c ∈ starImage H L := by
    have hm := le_normalizer_iff.mp hstar (q yH) ⟨yH, hy, rfl⟩
      (q lH) ⟨lH, hl, rfl⟩
    simpa only [c, map_mul, map_inv] using hm
  obtain ⟨b, hb, he⟩ := hc
  have hd : c * b⁻¹ ∈ pCore 2 H := by
    have hk : c * b⁻¹ ∈ q.ker := by
      change q (c * b⁻¹) = 1
      rw [map_mul, map_inv, ← he]
      exact mul_inv_cancel _
    simpa only [q, QuotientGroup.ker_mk'] using hk
  have hcJ : (c : G) ∈ J := le_normalizer_iff.mp hJ y hy l (hLJ hl)
  have hdL : ((c * b⁻¹ : H) : G) ∈ L :=
    hkernel ⟨J.mul_mem hcJ (J.inv_mem (hLJ hb)), ⟨c * b⁻¹, hd, rfl⟩⟩
  have hh := L.mul_mem hdL hb
  change (c : G) * (b : G)⁻¹ * (b : G) ∈ L at hh
  simpa [c, yH, lH] using hh

theorem commutator_le_twoCore_of_star_commutes
    (H L Y0 : Subgroup G) (hLH : L ≤ H) (hYH : Y0 ≤ H)
    (hn : Y0 ≤ normalizer (L : Set G))
    (hc : ⁅starImage H L, starImage H Y0⁆ = ⊥) :
    ⁅L, Y0⁆ ≤ localTwoCore L := by
  have hCH : ⁅L, Y0⁆ ≤ H := (Subgroup.commutator_le_sup L Y0).trans (sup_le hLH hYH)
  rw [← starImage_commutator H L Y0 hLH hYH] at hc
  have hCQ : ⁅L, Y0⁆ ≤ localTwoCore H := by
    have hi : (⁅L, Y0⁆).subgroupOf H ≤ pCore 2 H := by
      simpa only [starImage, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] using hc
    have hm := map_mono (f := H.subtype) hi
    simpa only [map_subgroupOf_eq_of_le hCH, localTwoCore] using hm
  exact (le_inf (le_normalizer_iff_commutator_le_left.mp hn) hCQ).trans
    (inf_pCoreIn_le_of_le 2 hLH)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration
