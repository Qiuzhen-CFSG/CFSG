module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowOvergroups.Overgroups
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.CentralNormalizerThreePart.PairQuotient
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.LargeNormalizerThreePart
public import Theory.GroupTheory.PrimeRankSquareFree
public import Theory.Quasithin.CoprimeRank
public import Theory.Quasithin.Rank
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Large odd-prime ranks in Higman–Sims Sylow overgroups

The exhaustive full-Sylow cover has two actual locals. The first maps to
S₅ with a two-group kernel. The second acts on an elementary group of
order at most eight, also with a two-group kernel. Its automorphism
group has order dividing 168. Neither image has a square factor at a
prime greater than three, so both locals have such prime rank at most one.

Source: Aschbacher–Smith A.3.12(18), printed pp.47–48; the imported
certificates retain the ATLAS HSG1-p100B0 carrier and literal normalizers.
-/

public noncomputable section
open Subgroup
namespace Sporadic.LeechRelated.HS.SylowOvergroups
open EvenLocalCandidates

private theorem large_prime_square_not_dvd {p : ℕ} (hp : p.Prime) (hl : 3 < p) :
    ¬ p ^ 2 ∣ 2 ^ 3 * 3 * 5 * 7 := by
  intro hd
  have hpdiv : p ∣ 2 ^ 3 * 3 * 5 * 7 := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hd
  rcases hp.dvd_mul.mp hpdiv with h | h
  · rcases hp.dvd_mul.mp h with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · have := Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two h
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
        omega
    · have he := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h
      subst p
      norm_num at hd
  · have he := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7)).mp h
    subst p
    norm_num at hd

private theorem rank_bound_of_two_kernel {A B : Type*} [Group A] [Finite A]
    [Group B] [Finite B] {p : ℕ} [Fact p.Prime] (hp : 3 < p) (ho : Odd p)
    (f : A →* B) (hk : IsPGroup 2 f.ker) (hc : Nat.card B ∣ 840) :
    primeRank p A ≤ 1 := by
  have hcop : Nat.Coprime p (Nat.card f.ker) := by
    obtain ⟨n,hn⟩ := hk.exists_card_eq
    rw [hn]
    exact (Nat.coprime_two_right.mpr ho).pow_right n
  apply (primeRank_le_of_coprime_ker p f hcop).trans
  apply primeRank_le_one_of_square_not_dvd
  intro hd
  exact large_prime_square_not_dvd Fact.out hp (hd.trans hc)

/-- The central-involution normalizer has large odd-prime rank at most one. -/
theorem central_local_primeRank_le_one {p : ℕ} [Fact p.Prime]
    (hp : 3 < p) (ho : Odd p) : primeRank p (localGroup 0) ≤ 1 := by
  apply rank_bound_of_two_kernel hp ho CentralNormalizerThreePart.PairQuotient.fiveHom
  · rw [CentralNormalizerThreePart.PairQuotient.fiveHom_kernel]
    exact CentralInvolutionCore.core_isPGroup
  · rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    norm_num

/-- The larger elementary normalizers also have large odd-prime rank at most one. -/
theorem large_local_primeRank_le_one (i : Fin 3) (hi : i ≠ 0)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (ho : Odd p) :
    primeRank p (localGroup i) ≤ 1 := by
  let E := elementary i
  let := elementary_isElementaryAbelian i
  apply rank_bound_of_two_kernel hp ho E.normalizerMonoidHom
  · rw [normalizerMonoidHom_ker]
    exact (large_elementary_centralizer_isPGroup i hi).of_equiv
      (subgroupOfEquivOfLe (centralizer_le_normalizer (E : Set Carrier))).symm
  · have hd : Nat.card (MulAut E) ∣ 168 := by
      obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
      have hnle : n ≤ 3 := by
        apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
        simpa only [← hn] using elementary_card_le_eight i
      rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow E n hn]
      interval_cases n <;> norm_num [Fin.prod_univ_succ]
    exact hd.trans (by norm_num)

/-- Every proper full-Sylow overgroup in the actual HS carrier has
p-rank at most one for p > 3. -/
theorem proper_overgroup_primeRank_le_one
    (S : Sylow 2 Carrier) (D : Subgroup Carrier)
    (hSD : (S : Subgroup Carrier) ≤ D) (hD : D ≠ ⊤)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (ho : Odd p) : primeRank p D ≤ 1 := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Carrier S BlockNormalizer.baseSylow
  let c := MulAut.conj g
  have hS : (S : Subgroup Carrier).map c.toMonoidHom = subgroup :=
    congrArg Sylow.toSubgroup hg
  have hDc : D.map c.toMonoidHom ≠ ⊤ := by
    intro he
    apply hD
    apply map_injective (f := c.toMonoidHom) c.injective
    rw [he,map_top_of_surjective _ c.surjective]
  apply (primeRank_congr p (c.subgroupMap D)).trans_le
  rcases proper_overgroup_le (D.map c.toMonoidHom) (hS ▸ map_mono hSD) hDc with h | h
  · exact (primeRank_mono p h).trans (central_local_primeRank_le_one hp ho)
  · exact (primeRank_mono p h).trans (large_local_primeRank_le_one 2 (by decide) hp ho)

end Sporadic.LeechRelated.HS.SylowOvergroups
