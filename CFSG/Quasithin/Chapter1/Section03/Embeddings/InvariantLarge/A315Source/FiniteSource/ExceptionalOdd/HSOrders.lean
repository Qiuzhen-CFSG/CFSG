module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.CentralNormalizerThreePart.PairQuotient
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.LargeNormalizerThreePart

/-!
# Five-parts of the actual Higman–Sims local normalizers

The first normalizer has a two-group kernel and the actual symmetric quotient
on five letters. The other two have two-group centralizers and act on elementary
groups of order at most eight. These exact actions exclude a divisor of 25.

Source: Aschbacher–Smith, Proposition 1.3.4, printed p.511;
GLS3 Table 5.3m for the actual HS local normalizers.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.ExceptionalOdd
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates

private theorem odd_divisor_of_two_kernel {G K : Type*} [Group G] [Group K] [Finite G]
    (f : G →* K) (hk : IsPGroup 2 f.ker) {m : ℕ} (hm : Nat.Coprime m 2)
    (hd : m ∣ Nat.card G) : m ∣ Nat.card K := by
  obtain ⟨n, hn⟩ := hk.exists_card_eq
  have hcop : Nat.Coprime m (Nat.card f.ker) := by rw [hn]; exact hm.pow_right n
  have hprod := f.ker.card_mul_index
  rw [index_ker] at hprod
  rw [← hprod] at hd
  exact (hcop.dvd_of_dvd_mul_left hd).trans f.range.card_subgroup_dvd_card

theorem hs_central_local_twentyfive_not_dvd : ¬ 25 ∣ Nat.card (localGroup 0) := by
  intro hd
  have hk : IsPGroup 2 CentralNormalizerThreePart.PairQuotient.fiveHom.ker := by
    rw [CentralNormalizerThreePart.PairQuotient.fiveHom_kernel]
    exact CentralInvolutionCore.core_isPGroup
  have hh := odd_divisor_of_two_kernel _ hk (by decide : Nat.Coprime 25 2) hd
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] at hh

theorem hs_large_local_twentyfive_not_dvd (i : Fin 3) (hi : i ≠ 0) :
    ¬ 25 ∣ Nat.card (localGroup i) := by
  let E := elementary i
  let _ := elementary_isElementaryAbelian i
  have hc : Nat.card (MulAut E) ∣ 168 := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
    have hnle : n ≤ 3 := by
      apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
      simpa only [← hn] using elementary_card_le_eight i
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow E n hn]
    interval_cases n <;> norm_num [Fin.prod_univ_succ]
  let f := E.normalizerMonoidHom
  have hk : IsPGroup 2 f.ker := by
    rw [normalizerMonoidHom_ker]
    exact (large_elementary_centralizer_isPGroup i hi).of_equiv
      (subgroupOfEquivOfLe (centralizer_le_normalizer (E : Set Carrier))).symm
  intro hd
  have hh := odd_divisor_of_two_kernel f hk (by decide : Nat.Coprime 25 2) hd
  exact (by decide : ¬ 25 ∣ 168) (hh.trans hc)
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.ExceptionalOdd
