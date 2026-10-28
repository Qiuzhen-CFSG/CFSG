module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Choice
public import CFSG.Quasithin.Chapter16.Section04To05.Fusion

/-!
# Elementary reductions in 16.4.9

Tight embedding excludes involutions in K ∩ J for J ∈ Δ. The inner-involution
detector then proves that J ∩ KL has odd order when J is outside Δ₀, conditional
on 16.4.9(1). This establishes the odd-intersection part of (*) in the contrary
empty-family case without assuming an involution fusion restriction.

For case (I) of the order argument, a bound on the residual centralizer modulo
K puts R inside K⟨r⟩. Faithfulness R ∩ K = 1 then gives R = ⟨r⟩ and |R| = 2.
The intrinsic centralizer bound and the exceptional cases are separate inputs.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
16.4.9, printed p.1189.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections

open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Distinct conjugates in Δ meet K in odd order. -/
theorem odd_centralizer_intersection_of_mem_delta {L J : Subgroup G}
    (htight : IsTightlyEmbedded (centralizer (L : Set G)))
    (hJ : J ∈ delta L) : Odd (Nat.card ↥(J ⊓ centralizer (L : Set G))) := by
  obtain ⟨⟨g, rfl⟩, hne, _⟩ := hJ
  have hg : g ∉ normalizer (centralizer (L : Set G) : Set G) := by
    intro hg
    exact hne (mem_normalizer_iff_map_conj_eq.mp hg)
  simpa only [Subgroup.conjBy, inf_comm] using htight.2 g hg

omit [Finite G] in
/-- No involution in a member of Δ centralizes L. -/
theorem involution_not_mem_centralizer_of_mem_delta {L J : Subgroup G}
    (htight : IsTightlyEmbedded (centralizer (L : Set G)))
    (hJ : J ∈ delta L) {i : G} (hi : i ∈ J) (hi2 : orderOf i = 2) :
    i ∉ centralizer (L : Set G) := by
  intro hiK
  have hodd := odd_centralizer_intersection_of_mem_delta htight hJ
  have hid : 2 ∣ Nat.card ↥(J ⊓ centralizer (L : Set G)) := by
    have horder : orderOf (⟨i, hi, hiK⟩ : ↥(J ⊓ centralizer (L : Set G))) = 2 :=
      (orderOf_coe _).symm.trans hi2
    exact horder ▸ orderOf_dvd_natCard _
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hid)

/-- The order bound implies the odd-intersection assertion in source (*). -/
theorem odd_componentProduct_intersection_of_not_mem_deltaZero {L J : Subgroup G}
    (htight : IsTightlyEmbedded (centralizer (L : Set G)))
    (hn : normalizer (centralizer (L : Set G) : Set G) = normalizer (L : Set G))
    (hsmall : OrderTwoOutsideDeltaZero L)
    (hJ : J ∈ delta L) (hnot : J ∉ deltaZero L) :
    Odd (Nat.card ↥(J ⊓ (centralizer (L : Set G) ⊔ L))) := by
  apply Nat.not_even_iff_odd.mp
  intro heven
  obtain ⟨i, hi⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
  have hi2 : orderOf (i : G) = 2 := (orderOf_coe i).trans hi
  exact hnot (mem_deltaZero_of_inner_involution hn hsmall hJ.1 i.property.1
    hi2 i.property.2 (involution_not_mem_centralizer_of_mem_delta htight hJ i.property.1 hi2))

omit [Finite G] in
/-- The faithful-centralizer argument in case (I) of source 16.4.9(1). -/
theorem sylow_card_two_of_centralizer_bound {L J R D : Subgroup G} {r : G}
    (hR : SylowIn R (J ⊓ normalizer (centralizer (L : Set G) : Set G)))
    (hfaithful : Disjoint R (centralizer (L : Set G)))
    (hcentralizes : R ≤ centralizer (D : Set G))
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hbound : normalizer (centralizer (L : Set G) : Set G) ⊓ centralizer (D : Set G) ≤
      centralizer (L : Set G) ⊔ zpowers r) : Nat.card R = 2 := by
  have hzR : zpowers r ≤ R := zpowers_le.mpr hr
  have hRN := hR.le.trans inf_le_right
  have heq : R = zpowers r := by
    apply le_antisymm ?_ hzR
    intro x hx
    have hxprod := hbound ⟨hRN hx, hcentralizes hx⟩
    change x ∈ (↑(centralizer (L : Set G) ⊔ zpowers r) : Set G) at hxprod
    rw [coe_mul_of_right_le_normalizer_left _ _ (hzR.trans hRN)] at hxprod
    obtain ⟨k, hk, a, ha, hka⟩ := hxprod
    have hkR : k ∈ R := by
      have hh := R.mul_mem hx (R.inv_mem (hzR ha))
      rwa [← hka, mul_inv_cancel_right] at hh
    have hk1 : k = 1 := Subgroup.disjoint_def.mp hfaithful hkR hk
    simp only [hk1, one_mul] at hka
    exact hka ▸ ha
  rw [heq, Nat.card_zpowers, hr2]

end CFSG.Quasithin.Chapter16.Intersections
