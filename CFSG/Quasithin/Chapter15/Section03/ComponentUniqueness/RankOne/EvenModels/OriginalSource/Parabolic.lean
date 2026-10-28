module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.Transport
/-!
# The original component intersection in the rank-one branch

The source normal four-group is contained in the component and normal in its
local intersection, so that intersection has nontrivial two-core. Minimality
of the actual outside overgroup also makes the intersection maximal among
proper component subgroups invariant under the original Sylow subgroup.
These facts apply before any model identification or centralizer placement.

Source: Aschbacher--Smith, 15.3.43(a)--(e), printed pp.1139--1140.
-/

public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.OriginalSource
variable {G : Type*} [Group G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}
variable (c : ReducedConfiguration Yplus S M I L V₁ V₂)
include c

private theorem proper_overgroup_le (J : Subgroup G)
    (hYJ : Yplus ⊔ S ≤ J) (hJI : J < I) : J ≤ M := by
  by_contra hJM
  obtain ⟨P, hP⟩ := c.sylow
  have hcore : I.pCoreIn 2 ≤ J.pCoreIn 2 := by
    apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 I)
    · exact (hP ▸ pCoreIn_le_sylow I P).trans (le_sup_right.trans hYJ)
    · exact hJI.le.trans (I.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image I (pCore 2 I)))
  have hJ : J ∈ outsideFamily Yplus S M := by
    refine ⟨⟨?_, hYJ⟩, hJM⟩
    intro he
    exact c.minimal.1.1.1 (bot_unique (he ▸ hcore))
  exact hJI.ne (c.minimal.eq_of_ge hJ hJI.le).symm

/-- Minimality in the original ambient group supplies invariant component maximality. -/
theorem invariant_component_overgroup_eq (K : Subgroup G) (hK : K < L)
    (hMK : M ⊓ L ≤ K) (hSK : S ≤ normalizer (K : Set G)) : K = M ⊓ L := by
  have hSI : S ≤ I := (sylow_le_local c).trans inf_le_right
  have hint : (K ⊔ S) ⊓ L = K := by
    apply le_antisymm ?_ (le_inf le_sup_left hK.le)
    intro x hx
    have hm : x ∈ (K : Set G) * (S : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left K S hSK]
      exact hx.1
    obtain ⟨k, hk, s, hs, he⟩ := hm
    have hsL : s ∈ L := by
      have hh := L.mul_mem (L.inv_mem (hK.le hk)) hx.2
      rw [← he, inv_mul_cancel_left] at hh
      exact hh
    exact he ▸ K.mul_mem hk (hMK ⟨c.sylow_le_M hs, hsL⟩)
  have hJI : K ⊔ S < I := by
    refine lt_of_le_of_ne (sup_le (hK.le.trans c.component_le) hSI) ?_
    intro he
    rw [he, inf_eq_right.mpr c.component_le] at hint
    exact hK.ne hint.symm
  have hY : Yplus ≤ M ⊓ L := by
    rw [ParabolicInspection.residual_on_component c]
    exact map_subtype_le _
  exact le_antisymm (le_inf
    (le_sup_left.trans (proper_overgroup_le c (K ⊔ S)
      (sup_le_sup (hY.trans hMK) le_rfl) hJI)) hK.le) hMK

/-- The original normal four-group supplies the local nonzero two-core. -/
theorem intersection_twoCore_ne_bot : pCore 2 (M.subgroupOf L) ≠ ⊥ := by
  let W := V₂.subgroupOf L
  have hVL : V₂ ≤ L := plane_le_component c
  have hWM : W ≤ M.subgroupOf L := fun _ hx => c.sylow_le_M (c.plane_two_le hx)
  have hn : M.subgroupOf L ≤ normalizer (W : Set L) := by
    rw [← subgroupOf_normalizer_eq hVL]
    exact fun x hx => c.plane_two_normalized ⟨hx, c.component_le x.property⟩
  let : IsElementaryAbelian 2 V₂ := c.plane_two_elementary
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hVL
  have hcore := le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 W) hWM hn
  intro he
  have hbot : W = ⊥ := bot_unique (by simpa [Subgroup.pCoreIn, he] using hcore)
  have hc : Nat.card W = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVL).toEquiv).trans c.plane_two_card
  rw [hbot, card_bot] at hc
  norm_num at hc
end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.OriginalSource
