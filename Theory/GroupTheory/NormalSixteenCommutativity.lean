module

public import Theory.GroupTheory.CenterSmallIndex
public import Theory.GroupTheory.Commutator.CentralDihedral
public import Theory.GroupTheory.NormalCenterQuotient
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# Commutativity at order sixteen from characteristic-subgroup exclusion

For a nonabelian group of order sixteen with center of order at least four,
the central quotient is a four-group and the derived subgroup has order two.
Thus excluding characteristic subgroups of order two forces commutativity.
A normal subgroup of a center-free ambient group satisfies this exclusion.
The intrinsic criterion also supports the fused-four argument in
Janko–Thompson, Math. Z. 113 (1970), p.393.
-/

open scoped commutatorElement

universe u

namespace NormalSixteenCommutativity

private theorem quotient_is_klein_four {H : Type*} [Group H] [Finite H]
    (hcard : Nat.card (H ⧸ Subgroup.center H) = 4)
    (hncyc : ¬ IsCyclic (H ⧸ Subgroup.center H)) :
    IsKleinFour (H ⧸ Subgroup.center H) := by
  let _ : Nontrivial (H ⧸ Subgroup.center H) :=
    (Finite.one_lt_card_iff_nontrivial).mp (by rw [hcard]; omega)
  refine ⟨hcard, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr ?_⟩
  intro x hx
  have hxdvd : orderOf x ∣ 4 := by
    rw [← hcard]
    exact orderOf_dvd_natCard x
  have hxone : orderOf x ≠ 1 := by simpa using hx
  have hxnotfour : orderOf x ≠ 4 := by
    intro hfour
    exact hncyc (isCyclic_of_orderOf_eq_card x (hfour.trans hcard.symm))
  obtain ⟨k, hk, hpow⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show orderOf x ∣ 2 ^ 2 by simpa using hxdvd)
  interval_cases k
  · exact (hxone hpow).elim
  · exact hpow
  · exact (hxnotfour hpow).elim

/-- A group of order sixteen with center of order at least four is abelian
if it has no characteristic subgroup of order two. -/
public theorem isMulCommutative_of_card_sixteen_of_no_characteristic_two
    {H : Type u} [Group H] [Finite H]
    (hcard : Nat.card H = 16)
    (hcenterCard : 4 ≤ Nat.card (Subgroup.center H))
    (hchar : ∀ K : Subgroup H, K.Characteristic → Nat.card K ≠ 2) :
    IsMulCommutative H := by
  by_contra hcomm
  have hderived : _root_.commutator H ≠ ⊥ :=
    (commutator_eq_bot_iff H).not.mpr hcomm
  have hindex : (Subgroup.center H).index ≤ 4 := by
    have hprod := (Subgroup.center H).card_mul_index
    rw [hcard] at hprod
    have hdiv := (Subgroup.center H).card_subgroup_dvd_card
    rw [hcard] at hdiv
    have hcenterle : Nat.card (Subgroup.center H) ≤ 16 :=
      Nat.le_of_dvd (by omega) hdiv
    nlinarith
  have hcenterEq := Subgroup.center_eq_and_index_four_of_central_small_index
    (Subgroup.center H) le_rfl hindex hderived
  have hquotCard : Nat.card (H ⧸ Subgroup.center H) = 4 := by
    rw [← (Subgroup.center H).index_eq_card, hcenterEq.2]
  let Q := H ⧸ Subgroup.center H
  let _ : IsKleinFour Q := quotient_is_klein_four hquotCard (fun hcyc =>
    hcomm (isMulCommutative_of_isCyclic_quotient_center_self H))
  let e : Q ≃* DihedralGroup 2 := IsKleinFour.nonempty_mulEquiv.some
  let f : H →* DihedralGroup 2 := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center H))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center H))
  have hker : f.ker ≤ Subgroup.center H := by
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    change e (QuotientGroup.mk' (Subgroup.center H) x) = 1 at hx
    exact e.injective (hx.trans e.map_one.symm)
  have hbound := CentralExtension.card_center_inf_commutator_le_two_of_dihedral f hf hker
  have hcommCenter : _root_.commutator H ≤ Subgroup.center H := by
    change ⁅(⊤ : Subgroup H), ⊤⁆ ≤ Subgroup.center H
    apply Subgroup.commutator_le.mpr
    intro x _ y _
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' (Subgroup.center H)) ⁅x, y⁆ = 1
    rw [map_commutatorElement]
    have hc := ((commutator_eq_bot_iff Q).mpr IsKleinFour.isMulCommutative :
      _root_.commutator Q = ⊥)
    have hm : ⁅(QuotientGroup.mk' (Subgroup.center H)) x,
        (QuotientGroup.mk' (Subgroup.center H)) y⁆ ∈ _root_.commutator Q :=
      Subgroup.commutator_mem_commutator trivial trivial
    rw [hc] at hm
    exact hm
  have hcommCard : Nat.card (_root_.commutator H) ≤ 2 := by
    rw [inf_eq_right.mpr hcommCenter] at hbound
    exact hbound
  have hcommCardEq : Nat.card (_root_.commutator H) = 2 := by
    have hnontriv : Nat.card (_root_.commutator H) ≠ 1 := by
      intro hone
      exact hderived (Subgroup.card_eq_one.mp hone)
    have hpos := Nat.card_pos (α := _root_.commutator H)
    omega
  exact hchar (_root_.commutator H) inferInstance hcommCardEq

public theorem isMulCommutative_of_normal_order_sixteen
    {G : Type u} [Group G] [Finite G] (whole : Subgroup G) [whole.Normal]
    (hcenter : Subgroup.center G = ⊥) (hcard : Nat.card whole = 16)
    (hcenterCard : 4 ≤ Nat.card (Subgroup.center whole)) :
    IsMulCommutative whole := by
  apply isMulCommutative_of_card_sixteen_of_no_characteristic_two hcard hcenterCard
  intro part hpart htwo
  let : part.Characteristic := hpart
  let ambient : Subgroup G := part.map whole.subtype
  let : ambient.Normal := ConjAct.normal_of_characteristic_of_normal
  have hambCard : Nat.card ambient = 2 :=
    (Subgroup.card_map_of_injective whole.subtype_injective).trans htwo
  have hambCenter := Subgroup.central_of_normal_card_two ambient hambCard
  have hambBot : ambient = ⊥ := le_bot_iff.mp (hcenter ▸ hambCenter)
  simp [hambBot] at hambCard

end NormalSixteenCommutativity
