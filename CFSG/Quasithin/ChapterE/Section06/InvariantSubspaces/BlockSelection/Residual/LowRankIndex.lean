module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Residual.Generation
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Residual.IndexContracts
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Residual.LowRankIndex.Contracts
public import Theory.GroupTheory.CyclicSylowSubnormalIndex
public import Theory.AtlasPort.LinearGroups.SL2Order

/-!
# The low-three-rank index calculation

The L₂(2ⁿ) and A₅ cases have three-torsion in their commutator subgroup.
Cyclic Sylow transfer, iterated along the subnormal chain, proves their
index is prime to three without an ambient normality assumption.

For the A₃ case, distinct commuting conjugates would supply an elementary
nine. Thus C.1.9 supplies relative normality at three-rank one. The final
conditional theorem combines this with the separate normal A₃ calculation.
The two pending inputs are explicit: this module does not yet assert the
unconditional `lowRankIndexInput` from Hypothesis E.6.1 and E.6.7.

All E.6.7 clauses remain in the imported contract, including its intermediate
characteristic-two decompositions. Neither count one nor generation alone
is used to exclude further three-elements.

Source: Aschbacher–Smith, E.6.7, printed p.246/PDF p.257; E.6.14,
printed p.251/PDF p.262; C.1.9 and C.1.12, printed pp.123–124.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection

private theorem core_quotient_three_dvd {L : Type*} [Group L]
    (h : ChapterC.IsChiZeroBlock L) : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
  let : Finite L := h.chi.short.finite
  obtain ⟨x, hx⟩ := exists_order_three h
  have hd : 3 ∣ Nat.card L := hx ▸ orderOf_dvd_natCard x
  have hc : Nat.Coprime 3 (Nat.card (pCore 2 L)) := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := L)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  rw [← (pCore 2 L).card_mul_index] at hd
  rw [← index_eq_card]
  exact (Nat.prime_three.dvd_mul.mp hd).resolve_left
    (Nat.prime_three.coprime_iff_not_dvd.mp hc)

private theorem derived_three_dvd_of_quasisimple_quotient {L : Type*} [Group L]
    (h : ChapterC.IsChiZeroBlock L) (hq : IsQuasisimple (L ⧸ pCore 2 L)) :
    3 ∣ Nat.card (_root_.commutator L) := by
  let : Finite L := h.chi.short.finite
  let := hq
  let q := QuotientGroup.mk' (pCore 2 L)
  have he : (_root_.commutator L).map q = ⊤ := by
    rw [_root_.commutator_def, map_commutator,
      map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
    exact Group.IsPerfect.commutator_eq_top
  have hd : Nat.card (L ⧸ pCore 2 L) ∣ Nat.card (_root_.commutator L) := by
    have hh := card_dvd_of_surjective (q.subgroupMap (_root_.commutator L))
      (q.subgroupMap_surjective (_root_.commutator L))
    simpa only [he, card_top] using hh
  exact (core_quotient_three_dvd h).trans hd

/-- Only the A₃ model can lack three-torsion in the block's derived group. -/
theorem chiZero_derived_three_dvd_or_alternatingThree {L : Type*} [Group L]
    (h : ChapterC.IsChiZeroBlock L) :
    3 ∣ Nat.card (_root_.commutator L) ∨ ChapterC.IsAlternatingBlock L 3 := by
  rcases h with ⟨n, hn⟩ | h | h
  · left
    apply derived_three_dvd_of_quasisimple_quotient (Or.inl ⟨n, hn⟩)
    rcases hn.2.1.quotient with hq | hq
    · exact hq
    · have hnge := hn.1
      obtain ⟨_, _, F, _, _, hF, _, hmodel⟩ := hn
      obtain ⟨e⟩ := hmodel.quotient_iso
      rw [Nat.card_congr e.toEquiv, Atlas.card_sl_two] at hq
      have hfour : 4 ≤ Nat.card F := by
        rw [hF]
        exact show 2 ^ 2 ≤ 2 ^ n from Nat.pow_le_pow_right (by decide) (by omega)
      have hs : 1 ≤ Nat.card F ^ 2 := by nlinarith
      have ht : 3 < Nat.card F * (Nat.card F ^ 2 - 1) := by
        nlinarith [Nat.sub_add_cancel hs]
      omega
  · exact Or.inr h
  · left
    apply derived_three_dvd_of_quasisimple_quotient (Or.inr (Or.inr h))
    rcases h.2.1.quotient with hq | hq
    · exact hq
    · obtain ⟨e⟩ := h.2.2.quotient_iso
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup] at hq
      norm_num at hq

variable {G : Type*} [Group G] [Finite G]

/-- The perfect-quotient branch, with only source relative subnormality.
The proof does not assume that Sylow three-subgroups lie in the block. -/
theorem chiZero_index_of_derived_three_dvd {H L : Subgroup G}
    (hLH : L ≤ H) (hL : ChapterC.IsChiZeroBlock L)
    (hsub : (L.subgroupOf H).IsSubnormal) (hrank : primeRank 3 H ≤ 1)
    (hd : 3 ∣ Nat.card (_root_.commutator L)) : Nat.Coprime 3 (L.relIndex H) := by
  let e := subgroupOfEquivOfLe hLH
  have hres : primeToResidual 3 (L.subgroupOf H) = ⊤ := by
    have he := map_primeToResidual (p := 3) e.symm
    rw [chiZero_primeToResidual_eq_top hL,
      map_top_of_surjective e.symm.toMonoidHom e.symm.surjective] at he
    exact he.symm
  have hd' : 3 ∣ Nat.card (_root_.commutator (L.subgroupOf H)) := by
    have he : (_root_.commutator (L.subgroupOf H)).map e.toMonoidHom =
        _root_.commutator L := by
      simp only [_root_.commutator_def, map_commutator,
        map_top_of_surjective e.toMonoidHom e.surjective]
    rwa [← he, card_map_of_injective e.injective] at hd
  exact coprime_index_of_subnormal_primeToResidual_of_rank_one (L.subgroupOf H)
    hsub hres (by decide) hrank hd'

/-- At three-rank one, the C.1.9 commutation conclusion makes the selected
block normal. The actor is arbitrary, including higher three-power roots. -/
theorem chiZero_normal_of_rank_one_of_conjugate_commutation {H L : Subgroup G}
    (hLH : L ≤ H) (hL : ChapterC.IsChiZeroBlock L) (hrank : primeRank 3 H ≤ 1)
    (hcomm : ∀ x ∈ H, L.map (MulAut.conj x) ≠ L →
      L.map (MulAut.conj x) ≤ centralizer (L : Set G)) :
    (L.subgroupOf H).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  intro x hx
  by_contra hn
  have hc := hcomm x hx (fun he => hn (mem_normalizer_iff_map_conj_eq.mpr he))
  obtain ⟨a, ha⟩ := exists_order_three hL
  let b := MulAut.conj x (a : G)
  have haG : orderOf (a : G) = 3 := (Subgroup.orderOf_coe a).trans ha
  have hbG : orderOf b = 3 := (MulAut.conj x).orderOf_eq a |>.trans haG
  have hbL : b ∈ L.map (MulAut.conj x) := mem_map_of_mem _ a.property
  obtain ⟨hE, hcard⟩ := nine_of_commuting_threes hL.chi.short hc
    a.property hbL haG hbG
  let E := zpowers (a : G) ⊔ zpowers b
  let : IsElementaryAbelian 3 E := hE
  have hEH : E ≤ H := sup_le (zpowers_le.mpr (hLH a.property))
    (zpowers_le.mpr (H.mul_mem (H.mul_mem hx (hLH a.property)) (H.inv_mem hx)))
  let : IsElementaryAbelian 3 (E.subgroupOf H) := IsElementaryAbelian.subgroupOf hEH
  have htwo : 2 ≤ primeRank 3 H :=
    IsElementaryAbelian.primeRank_ge_of_card (E.subgroupOf H)
      ((Nat.card_congr (subgroupOfEquivOfLe hEH).toEquiv).trans hcard)
  omega

/-- Conditional assembly, retaining the unproved A₃ structural inputs explicitly.
The L₂ and A₅ branches are already discharged by transfer. -/
theorem lowRankIndexInput_of_alternatingThree_inputs
    {T : Sylow 2 G} {M V : Subgroup G}
    (hcomm : AlternatingThreeConjugateCommutationInput G)
    (hindex : AlternatingThreeNormalIndexInput G) : LowRankIndexInput T M V := by
  intro W _ hchar hrank d _ i
  rcases chiZero_derived_three_dvd_or_alternatingThree (d.type i) with hd | ha
  · exact chiZero_index_of_derived_three_dvd (d.le i) (d.type i) (d.subnormal i) hrank hd
  · have hn := chiZero_normal_of_rank_one_of_conjugate_commutation (d.le i)
      (d.type i) hrank (hcomm _ _ hchar (d.le i) ha (d.subnormal i))
    exact hindex _ _ (d.le i) ha hn hrank

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
