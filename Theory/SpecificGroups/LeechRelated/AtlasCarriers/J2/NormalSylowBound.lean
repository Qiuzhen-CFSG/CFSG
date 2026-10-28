module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.NormalElementaryBound
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.Automorphisms.Full
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.GroupTheory.NormalSylowElementaryBound
public import Mathlib.GroupTheory.IndexNormal

/-!
# Hall–Janko normal elementary actors in inner and outer extensions

The inner carrier has index two in the certified full automorphism extension.
A normal elementary actor in a Sylow subgroup meets the inner carrier in
order at most four, so its order is at most eight. Every overgroup of the
inner carrier is either that carrier or the full extension.

Source: GLS3 Table 5.3g and Aschbacher–Smith G.11.1(4), G.11.7.
-/

public section
open Subgroup Theory.GroupTheory
namespace Sporadic.LeechRelated.J2
open ExceptionalParabolics

theorem inner_extension_index : intoExtension.range.index = 2 := by
  have hc : Nat.card intoExtension.range = 604800 :=
    (Nat.card_congr (MonoidHom.ofInjective SecondParabolic.intoExtension_injective).toEquiv).symm.trans
      (SecondParabolic.card_carrier FirstParabolic.card_l₁)
  have h := intoExtension.range.card_mul_index
  rw [hc,SecondParabolic.card_extension FirstParabolic.card_l₁] at h
  omega

theorem extension_sylow_normal_elementary_card_le_eight (P : Sylow 2 Extension)
    (E : Subgroup P) (hn : E.Normal) (he : IsElementaryAbelian 2 E) : Nat.card E ≤ 8 := by
  let N := intoExtension.range
  have hi : N.index = 2 := inner_extension_index
  let : N.Normal := N.normal_of_index_eq_two hi
  let a : N ≃* Carrier := (MonoidHom.ofInjective SecondParabolic.intoExtension_injective).symm
  let R := E.map (P : Subgroup Extension).subtype
  let : IsElementaryAbelian 2 E := he
  let : IsElementaryAbelian 2 R := IsElementaryAbelian.map _
  have hRn : (R.subgroupOf (P : Subgroup Extension)).Normal := by
    have hEq : R.subgroupOf (P : Subgroup Extension) = E :=
      comap_map_eq_self_of_injective (P : Subgroup Extension).subtype_injective E
    rw [hEq]
    exact hn
  have h := NormalSylowElementary.card_le_mul_index N 4
    (NormalSylowElementary.bound_equiv a 4 sylow_normal_elementary_card_le_four)
    P R (map_subtype_le E) hRn
  rw [hi,card_map_of_injective (P : Subgroup Extension).subtype_injective] at h
  exact h


/-- The same bound in every actual intermediate automorphism group. -/
theorem overgroup_sylow_normal_elementary_card_le_eight
    (D : Subgroup Extension) (hD : intoExtension.range ≤ D) :
    ∀ (Q : Sylow 2 D) (E : Subgroup Q), E.Normal →
      IsElementaryAbelian 2 E → Nat.card E ≤ 8 := by
  have hcases : D = intoExtension.range ∨
    D = ⊤ := by
    have hd := index_dvd_of_le hD
    rw [inner_extension_index] at hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact .inr (index_eq_one.mp h)
    · have hm := relIndex_mul_index hD
      rw [h,inner_extension_index] at hm
      exact .inl (le_antisymm (relIndex_eq_one.mp (by omega)) hD)
  rcases hcases with h | h
  · let a := (MulEquiv.subgroupCongr h).trans
      (MonoidHom.ofInjective
        SecondParabolic.intoExtension_injective).symm
    intro Q E hn he
    exact (NormalSylowElementary.bound_equiv a 4
      sylow_normal_elementary_card_le_four Q E hn he).trans (by decide)
  · exact NormalSylowElementary.bound_equiv
      ((MulEquiv.subgroupCongr h).trans Subgroup.topEquiv) 8
      extension_sylow_normal_elementary_card_le_eight

end Sporadic.LeechRelated.J2
