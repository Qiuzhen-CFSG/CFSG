module
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.PerfectCentralCoverAbelianSylow
public import Theory.GroupTheory.PrimeRankZero

/-!
# Rank zero for a perfect residual commuting with a full local factor

A perfect finite group of odd-prime rank at most one has cyclic Sylow
subgroups at that prime. Central transfer makes its centre prime to that
prime. In the quotient by the full two-core of a normalized factor, apply
rank addition with the perfect residual as the second factor. A factor of
rank at least two in a join of rank at most two forces the other rank to
vanish. In particular a cubic centre on the local factor is retained.

The relative version works in the actual join, transporting the residual,
commutator and intrinsic two-core through the literal inclusions.
Source application: Aschbacher--Smith, proof of 8.2.9(3), printed p.720,
refs/quasithin.pdf. The Chapter12 application supplies perfectness using
nonsolvability of the original minimal parabolic.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.ResidualCentralizerRank
variable {G : Type*} [Group G] [Finite G]

/-- Cyclic odd Sylow subgroups and perfectness exclude central prime torsion. -/
theorem center_coprime_of_perfect_odd_rank_one
    {p : ℕ} [Fact p.Prime] [Group.IsPerfect G] (ho : Odd p)
    (hr : primeRank p G ≤ 1) : Nat.Coprime p (Nat.card (center G)) := by
  let P : Sylow p G := default
  let : IsCyclic P := P.isCyclic_of_odd_of_primeRank_le_one ho hr
  have hh := PerfectCentralCovering.not_dvd_card_kernel_of_abelian_sylow
    (QuotientGroup.mk' (center G)) (by rw [QuotientGroup.ker_mk']) P inferInstance
  rw [QuotientGroup.ker_mk'] at hh
  exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hh

/-- A full normal factor of rank two exhausts the available odd rank. -/
theorem rank_zero_of_perfect_residual_normal_factor
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (H K : Subgroup G) [K.Normal] [Group.IsPerfect (pResidual 2 H)]
    (hc : ⁅(pResidual 2 H).map H.subtype, K⁆ ≤ K.pCoreIn 2)
    (hH : primeRank p H ≤ 1) (hK : 2 ≤ primeRank p K)
    (hG : primeRank p G ≤ 2) : primeRank p H = 0 := by
  let : (K.pCoreIn 2).Normal :=
    inferInstanceAs (((pCore 2 K).map K.subtype).Normal)
  let q := QuotientGroup.mk' (K.pCoreIn 2)
  let R := ((pResidual 2 H).map H.subtype).map q
  let B := K.map q
  let : Group.IsPerfect ((pResidual 2 H).map H.subtype) := Group.IsPerfect.map H.subtype
  let : Group.IsPerfect R := Group.IsPerfect.map q
  have hq : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact isPGroup_pCoreIn 2 K
  have hcomm : R ≤ centralizer (B : Set _) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hc
  have hR : primeRank p R = primeRank p H := by
    rw [primeRank_map_of_twoGroup_kernel ho q hq,
      ← primeRank_congr p ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective),
      primeRank_residual (Nat.coprime_two_left.mpr ho)]
  have hB : primeRank p B = primeRank p K :=
    primeRank_map_of_twoGroup_kernel ho q hq K
  have hz : Nat.Coprime p (Nat.card (center R)) :=
    center_coprime_of_perfect_odd_rank_one ho (hR ▸ hH)
  have hh := primeRank_add_le_of_center_coprime B R (le_centralizer_iff.mp hcomm) hz
  have hu := (primeRank_quotient_le_of_isTwoGroup p ho _
    (isPGroup_pCoreIn 2 K)).trans hG
  rw [hR,hB] at hh
  omega

private theorem residual_commutator_subgroupOf (H K : Subgroup G)
    (hc : ⁅(pResidual 2 H).map H.subtype, K⁆ ≤ K.pCoreIn 2) :
    ⁅(pResidual 2 (H.subgroupOf (H ⊔ K))).map (H.subgroupOf (H ⊔ K)).subtype,
      K.subgroupOf (H ⊔ K)⁆ ≤ (K.subgroupOf (H ⊔ K)).pCoreIn 2 := by
  let J := H ⊔ K
  let e := subgroupOfEquivOfLe (show K ≤ J from le_sup_right)
  apply (map_le_map_iff_of_injective J.subtype_injective).mp
  rw [map_commutator_embedded_pResidual, map_subgroupOf_eq_of_le le_sup_left,
    map_subgroupOf_eq_of_le le_sup_right]
  have he : J.subtype.comp (K.subgroupOf J).subtype = K.subtype.comp e.toMonoidHom := rfl
  change ⁅(pResidual 2 H).map H.subtype, K⁆ ≤
    ((pCore 2 (K.subgroupOf J)).map (K.subgroupOf J).subtype).map J.subtype
  rw [map_map, he, ← map_map, pCore_map_iso]
  exact hc

/-- Relative normality suffices; the conclusion concerns the original H. -/
theorem rank_zero_of_perfect_residual_normalized_factor
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (H K : Subgroup G) [Group.IsPerfect (pResidual 2 H)]
    (hn : H ≤ normalizer (K : Set G))
    (hc : ⁅(pResidual 2 H).map H.subtype, K⁆ ≤ K.pCoreIn 2)
    (hH : primeRank p H ≤ 1) (hK : 2 ≤ primeRank p K)
    (hG : primeRank p (H ⊔ K : Subgroup G) ≤ 2) : ¬ p ∣ Nat.card H := by
  let J := H ⊔ K
  let eH := subgroupOfEquivOfLe (show H ≤ J from le_sup_left)
  let eK := subgroupOfEquivOfLe (show K ≤ J from le_sup_right)
  let : (K.subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le hn K.le_normalizer)
  have hp : Group.IsPerfect ((pResidual 2 H).map eH.symm.toMonoidHom) :=
    Group.IsPerfect.map eH.symm.toMonoidHom
  rw [map_pResidual_of_surjective 2 eH.symm.toMonoidHom eH.symm.surjective] at hp
  let := hp
  have hh := rank_zero_of_perfect_residual_normal_factor ho
    (H.subgroupOf J) (K.subgroupOf J) (residual_commutator_subgroupOf H K hc)
    (by rwa [primeRank_congr p eH]) (by rwa [primeRank_congr p eK]) hG
  rw [primeRank_congr p eH] at hh
  exact PrimeRank.eq_zero_iff_not_dvd_card.mp hh

end Theory.GroupTheory.ResidualCentralizerRank
