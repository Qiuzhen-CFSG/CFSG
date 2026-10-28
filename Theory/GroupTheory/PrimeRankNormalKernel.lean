module
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.PrimeRankZero
public import Theory.GroupTheory.NormalSubgroupCoreQuotient

/-!
# A normal centralizer with no three-part

Suppose two normal subgroups intersect only inside the ambient two-core,
and one has three-rank at least two. In an ambient group of three-rank at
most two, the other subgroup has order prime to three. Map both groups
into the two-core quotient: their images are disjoint normal subgroups,
so they commute and their three-ranks add. Coprime lifting preserves the
three-ranks across the two-kernels.

This supplies the ordinary residual-kernel instance in Aschbacher--Smith,
15.3.49(4)--(5), printed pp.1142--1143.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {H : Type*} [Group H] [Finite H]

/-- The normal subgroup disjoint from a full-rank residual modulo O₂
has order prime to three. -/
theorem coprime_three_card_of_normal_disjoint_mod_core
    (N C : Subgroup H) [N.Normal] [C.Normal]
    (hQC : pCore 2 H ≤ C) (hNC : N ⊓ C ≤ pCore 2 H)
    (hN : 2 ≤ primeRank 3 N) (hH : primeRank 3 H ≤ 2) :
    Nat.Coprime 3 (Nat.card C) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let A := N.map q
  let B := C.map q
  let : A.Normal := (inferInstance : N.Normal).map q (QuotientGroup.mk'_surjective _)
  let : B.Normal := (inferInstance : C.Normal).map q (QuotientGroup.mk'_surjective _)
  have hq : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hd : Disjoint A B := by
    apply disjoint_iff.mpr
    apply eq_bot_iff.mpr
    rintro x ⟨⟨n, hn, rfl⟩, hxC⟩
    have hnC : n ∈ C := by
      have hh : n ∈ (C.map q).comap q := hxC
      rwa [comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hQC] at hh
    exact (QuotientGroup.eq_one_iff n).mpr (hNC ⟨hn, hnC⟩)
  have hcomm : A ≤ centralizer (B : Set (H ⧸ pCore 2 H)) :=
    commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_disjoint hd)
  have hr := primeRank_subgroup_le 3 (A ⊔ B)
  rw [primeRank_sup_eq_add_of_disjoint_commuting A B hd hcomm,
    ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide) q hq,
    ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide) q hq] at hr
  have hu := (primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 H)
    pCore_isPGroup).trans hH
  have hzero : primeRank 3 C = 0 := by omega
  exact Nat.prime_three.coprime_iff_not_dvd.mpr
    (PrimeRank.eq_zero_iff_not_dvd_card.mp hzero)
end Theory.GroupTheory
