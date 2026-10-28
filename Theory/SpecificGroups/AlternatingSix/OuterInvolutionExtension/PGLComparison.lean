module

public import Theory.SpecificGroups.AlternatingSix.OuterInvolutionExtension.Exceptional
public import Theory.SpecificGroups.AlternatingSix.OuterInvolutionExtension.ActionTransport
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order360
public import GorensteinWalter.PGL2LowTorus

/-!
# The canonical exceptional A₆ extension is PGL₂(9)

The canonical PSL₂(9) image in PGL₂(9) is self-centralizing and has index
two. An involution outside this image therefore generates the whole group
together with it, and conjugation gives a faithful extension action on A₆
through the actual PSL₂(9)–A₆ equivalence.

This actor cannot belong to the natural S₆: otherwise the whole faithful
image would lie in S₆, contradicting the order-eight generator of the split
torus. Cycle lengths show that S₆ has no element of order eight. The proved
conjugacy theorem for exceptional involutions then identifies this concrete
PGL₂(9) image with `canonicalExtension`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
16.4.9(2), printed p.1192 (PDF p.1209), the exceptional extension alternative.
The exceptional conjugacy input is GLS, Volume 3, Proposition 5.2.7(a).
-/

public section

open Subgroup Equiv
open AlternatingSix.ShadowLocal
open Atlas.Comparisons.Exceptional GorensteinWalter

namespace AlternatingSix.OuterInvolutionExtension

private theorem perm_six_order_ne_eight (s : Perm (Fin 6)) : orderOf s ≠ 8 := by
  intro h
  have hd : orderOf s ∣ 4 := by
    rw [← s.lcm_cycleType, Multiset.lcm_dvd]
    intro n hn
    have hnd : n ∣ 8 := h ▸ Equiv.Perm.dvd_of_mem_cycleType hn
    have hns : n ≤ s.cycleType.sum := Multiset.le_sum_of_mem hn
    have hsum : s.cycleType.sum ≤ 6 := s.sum_cycleType_le
    have hn6 : n ≤ 6 := hns.trans hsum
    interval_cases n <;> norm_num at hnd <;> norm_num
  norm_num [h] at hd

private theorem natural_order_ne_eight (a : AutA6) (ha : a ∈ natural) :
    orderOf a ≠ 8 := by
  obtain ⟨s, rfl⟩ := ha
  change orderOf (permutationAction s) ≠ 8
  rw [orderOf_injective permutationAction permutationAction_injective]
  exact perm_six_order_ne_eight s

private theorem index_two_sup_zpowers {G : Type*} [Group G]
    (H : Subgroup G) (hH : H.index = 2) (s : G) (hs : s ∉ H) :
    H ⊔ zpowers s = ⊤ := by
  apply top_unique
  intro x _
  by_cases hx : x ∈ H
  · exact mem_sup_left hx
  · have hxs : x * s⁻¹ ∈ H :=
      (H.mul_mem_iff_of_index_two hH).mpr (iff_of_false hx (by simpa using hs))
    have hm := (H ⊔ zpowers s).mul_mem (mem_sup_left hxs)
      (mem_sup_right (mem_zpowers s))
    simpa using hm

private theorem nine_odd_prime_power : IsOddPrimePower (Nat.card Nine.F) := by
  rw [Nine.card]
  exact ⟨3, 2, by decide, by decide, by decide, by decide⟩

private theorem nine_card_gt_three : 3 < Nat.card Nine.F := by
  rw [Nine.card]
  decide

private theorem pgl_nine_has_order_eight : ∃ x : PGL2 Nine.F, orderOf x = 8 := by
  obtain ⟨U, _, hcyc, hcard, _⟩ := pgl2_split_torus_reflection_data Nine.F
  let : IsCyclic U := hcyc
  obtain ⟨x, hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := U)
  refine ⟨x, ?_⟩
  rw [Subgroup.orderOf_coe, hx, hcard, Nine.card]

/-- The canonical exceptional involution extension is the actual projective
linear group over the fixed nine-element field. -/
theorem canonicalExtension_equiv_pgl2 :
    Nonempty (canonicalExtension ≃* PGL2 Nine.F) := by
  let : Finite (PGL2 Nine.F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let L : Subgroup (PGL2 Nine.F) :=
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := Nine.F)).range
  have hindex : L.index = 2 := pgl2_psl2Range_index_eq_two Nine.F nine_odd_prime_power
  let : L.Normal := Subgroup.normal_of_index_eq_two hindex
  let e : L ≃* A6 := (psl2EquivToPGLRange Nine.F).symm.trans psl2NineCoordinatesEquivAlt6
  obtain ⟨_, s, _, _, _, _, _, _, hsout, hsne, hssq, _⟩ :=
    pgl2_low_two_part_torus_reflection_data Nine.F nine_odd_prime_power nine_card_gt_three
  have hsL : s ∉ L := by
    dsimp only [L]
    rw [← pgl2_commutator_eq_psl2_range_of_card_gt_three
      Nine.F nine_odd_prime_power nine_card_gt_three]
    exact hsout
  have hsN : s ∈ normalizer (L : Set (PGL2 Nine.F)) := by
    rw [L.normalizer_eq_top]
    trivial
  have hs2 : orderOf s = 2 := orderOf_eq_prime (by simpa [pow_two] using hssq) hsne
  have hsC : s ∉ centralizer (L : Set (PGL2 Nine.F)) ⊔ L := by
    have hc := pgl2_psl2Range_centralizer_eq_bot Nine.F nine_odd_prime_power
    change centralizer (L : Set (PGL2 Nine.F)) = ⊥ at hc
    simpa [hc] using hsL
  have hgen : L ⊔ zpowers s = ⊤ := index_two_sup_zpowers L hindex s hsL
  let β : AutA6 := normalizerAction e ⟨s, hsN⟩
  let eg : ↥(L ⊔ zpowers s) ≃* PGL2 Nine.F :=
    (MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv
  let ea : ↥(L ⊔ zpowers s) ≃* ↥(ShadowLocal.inner ⊔ zpowers β) :=
    extensionEquiv e hsN hs2 hsC
  have hn : β ∉ natural := by
    intro hβ
    have hle : ShadowLocal.inner ⊔ zpowers β ≤ natural :=
      sup_le inner_le_natural (zpowers_le.mpr hβ)
    obtain ⟨x, hx⟩ := pgl_nine_has_order_eight
    let a := ea (eg.symm x)
    have ha : orderOf (a : AutA6) = 8 := by
      change orderOf (ea (eg.symm x) : AutA6) = 8
      rw [Subgroup.orderOf_coe, ea.orderOf_eq, eg.symm.orderOf_eq, hx]
    exact natural_order_ne_eight a (hle a.property) ha
  obtain ⟨ec⟩ := exceptional_extension_equiv_canonical β
    (normalizerAction_sq e hsN (by simpa [pow_two] using hssq)) hn
  exact ⟨(ec.symm.trans ea.symm).trans eg⟩

end AlternatingSix.OuterInvolutionExtension
