module
public import Theory.Quasithin.ComponentRanks
public import Theory.GroupTheory.GeneralizedFitting.ComponentProductCenters
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankZero
public import Theory.GroupTheory.CubicIntersectionRankLower
/-!
# Center coincidence and generation by two components

Two distinct components commute. If their centers have order three, a
center outside the other factor would contribute an independent third
rank inside a normalizer of a nontrivial two-subgroup. Quasithinness rules
this out, forcing the two embedded centers to coincide.

Likewise, a rank-three product of two components leaves no third component:
a nontrivial two-subgroup of that third component would be centralized by
the whole rank-three product. In a semisimple group the two components
therefore generate the ambient group.

Source: Aschbacher–Smith A.2.12(II), printed p.37.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem IsComponent.exists_nontrivial_two_subgroup
    {C : Subgroup G} (hC : IsComponent G C) :
    ∃ Q : Subgroup C, IsPGroup 2 Q ∧ Q ≠ ⊥ := by
  let := hC.2
  let : IsSimpleGroup (C ⧸ center C) := IsQuasisimple.simple
  let : Nontrivial C := (QuotientGroup.mk'_surjective (center C)).nontrivial
  have he : 2 ∣ Nat.card C := by
    by_contra hn
    exact Group.IsPerfect.not_isSolvable C
      (odd_order_theorem C (Nat.not_even_iff_odd.mp (by
        simpa only [even_iff_two_dvd] using hn)))
  let Q : Sylow 2 C := Classical.choice inferInstance
  exact ⟨Q, Q.isPGroup', Q.ne_bot_of_dvd_card he⟩

theorem IsComponent.centers_eq_of_cubic_centers
    {C D : Subgroup G} (hC : IsComponent G C) (hD : IsComponent G D) (hne : C ≠ D)
    (hG : IsQuasithin G) (hzC : Nat.card (center C) = 3)
    (hzD : Nat.card (center D) = 3) (hrD : 2 ≤ primeRank 3 D) :
    (center C).map C.subtype = (center D).map D.subtype := by
  let ZC := (center C).map C.subtype
  let ZD := (center D).map D.subtype
  have hc : C ≤ centralizer (D : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (hC.commutator_eq_bot_of_ne hD hne)
  have hZC : ZC ≤ C := map_subtype_le _
  have hcC : Nat.card ZC = 3 := (card_map_of_injective C.subtype_injective).trans hzC
  have hcD : Nat.card ZD = 3 := (card_map_of_injective D.subtype_injective).trans hzD
  by_contra he
  have hnot : ¬ ZC ≤ D := by
    intro hzCD
    have hZZ : ZC ≤ ZD := by
      intro z hz
      refine ⟨⟨z, hzCD hz⟩, ?_, rfl⟩
      apply mem_center_iff.mpr
      intro d
      exact Subtype.ext (hc (hZC hz) d d.property)
    exact he (eq_of_le_of_card_ge hZZ (by rw [hcC, hcD]))
  have hd : Disjoint ZC D := by
    apply disjoint_iff.mpr
    have hv : Nat.card (ZC ⊓ D : Subgroup G) ∣ 3 :=
      hcC ▸ card_dvd_of_le (inf_le_left : ZC ⊓ D ≤ ZC)
    rcases (Nat.dvd_prime Nat.prime_three).mp hv with hone | hthree
    · exact card_eq_one.mp hone
    · have heq : ZC ⊓ D = ZC := eq_of_le_of_card_ge inf_le_left (by rw [hthree, hcC])
      exact (hnot (heq.symm.le.trans inf_le_right)).elim
  obtain ⟨Q, hQ, hQne⟩ := hC.exists_nontrivial_two_subgroup
  let R := Q.map C.subtype
  let N := normalizer (R : Set G)
  have hZN : ZC ≤ N :=
    (map_mono (center_le_normalizer (Q : Set C))).trans (le_normalizer_map C.subtype)
  have hDN : D ≤ N := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro d hd r hr
    exact (hc (map_subtype_le Q hr) d hd).symm
  have hcc : ZC ≤ centralizer (D : Set G) := hZC.trans hc
  have hsum := ZC.primeRank_sup_eq_add_of_disjoint_commuting D hd hcc 3
  have hrZ : 1 ≤ primeRank 3 ZC := by
    by_contra hh
    have hz : primeRank 3 ZC = 0 := by omega
    have := PrimeRank.eq_zero_iff_not_dvd_card.mp hz
    rw [hcC] at this
    exact this (dvd_refl 3)
  have hle := primeRank_mono 3 (sup_le hZN hDN)
  rw [hsum] at hle
  have hRne : R ≠ ⊥ := fun hh => hQne
    ((map_eq_bot_iff_of_injective Q C.subtype_injective).mp hh)
  have hsmall := isQuasithin_iff_twoLocal.mp hG N
    ⟨R, hRne, hQ.map C.subtype, rfl⟩ 3 Nat.prime_three (by decide)
  omega

theorem IsComponent.sup_eq_top_of_rank_three
    {C D : Subgroup G} (hC : IsComponent G C) (hD : IsComponent G D)
    (hsemi : componentLayer G = ⊤) (hG : IsQuasithin G)
    (hr : 3 ≤ primeRank 3 (C ⊔ D : Subgroup G)) : C ⊔ D = ⊤ := by
  apply top_unique
  rw [← hsemi]
  apply sSup_le
  intro E hE
  by_cases heC : E = C
  · exact heC ▸ le_sup_left
  by_cases heD : E = D
  · exact heD ▸ le_sup_right
  obtain ⟨Q, hQ, hQne⟩ := hE.exists_nontrivial_two_subgroup
  let R := Q.map E.subtype
  let N := normalizer (R : Set G)
  have hCN : C ≤ N :=
    ((commutator_eq_bot_iff_le_centralizer.mp
      (hC.commutator_eq_bot_of_ne hE (Ne.symm heC))).trans
        (centralizer_le (map_subtype_le Q))).trans (Subgroup.centralizer_le_normalizer _)
  have hDN : D ≤ N :=
    ((commutator_eq_bot_iff_le_centralizer.mp
      (hD.commutator_eq_bot_of_ne hE (Ne.symm heD))).trans
        (centralizer_le (map_subtype_le Q))).trans (Subgroup.centralizer_le_normalizer _)
  have hRne : R ≠ ⊥ := fun hh => hQne
    ((map_eq_bot_iff_of_injective Q E.subtype_injective).mp hh)
  have hsmall := isQuasithin_iff_twoLocal.mp hG N
    ⟨R, hRne, hQ.map E.subtype, rfl⟩ 3 Nat.prime_three (by decide)
  have hbig := hr.trans (primeRank_mono 3 (sup_le hCN hDN))
  omega

theorem IsComponent.sup_eq_top_of_cubic_intersection
    {C D : Subgroup G} (hC : IsComponent G C) (hD : IsComponent G D) (hne : C ≠ D)
    (hsemi : componentLayer G = ⊤) (hG : IsQuasithin G)
    (hI : Nat.card (C ⊓ D : Subgroup G) ≤ 3)
    (hrC : 2 ≤ primeRank 3 C) (hrD : 2 ≤ primeRank 3 D) : C ⊔ D = ⊤ := by
  let N := C ⊔ D
  have hCN : C ≤ N := le_sup_left
  have hDN : D ≤ N := le_sup_right
  have hc : C ≤ centralizer (D : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (hC.commutator_eq_bot_of_ne hD hne)
  have hcN : C.subgroupOf N ≤ centralizer (D.subgroupOf N : Set N) := by
    intro x hx y hy
    exact Subtype.ext (hc hx y hy)
  have hiN : Nat.card (C.subgroupOf N ⊓ D.subgroupOf N : Subgroup N) ≤ 3 := by
    change Nat.card ((C ⊓ D).subgroupOf N) ≤ 3
    rw [Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hCN)).toEquiv]
    exact hI
  have hCr : 2 ≤ primeRank 3 (C.subgroupOf N) := by
    rw [primeRank_equiv 3 (subgroupOfEquivOfLe hCN)]
    exact hrC
  have hDr : 2 ≤ primeRank 3 (D.subgroupOf N) := by
    rw [primeRank_equiv 3 (subgroupOfEquivOfLe hDN)]
    exact hrD
  exact hC.sup_eq_top_of_rank_three hD hsemi hG
    (three_le_primeRank_of_cubic_intersection _ _ hcN hiN hCr hDr)
end Theory.GroupTheory
