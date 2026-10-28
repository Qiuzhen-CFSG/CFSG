module
public import Theory.GroupAction.ModelConjugation
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import Theory.GroupTheory.PrimeRankSquareFree
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow
public import Theory.Quasithin.CoprimeRank

/-!
# A binary action with five-rank two has dimension at least eight

A finite group acting on an elementary abelian two-group with a two-group
kernel retains its five-rank in the automorphism group. The orders of
GL(d,2), for d at most seven, have five-part at most five. An actor of
five-rank at least two therefore forces ambient two-rank at least eight.
If the ambient two-core is trivial, its center has odd order and the same
bound survives in the central quotient.

This is the elementary rank obstruction used for the original A5 pair in
Aschbacher--Smith 4.4.12 and 10.2.3, printed pp.622 and745.
-/

public section
open Subgroup
namespace Theory.GroupAction

private theorem small_elementary_automorphism_five_rank
    (E : Type*) [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hc : Nat.card E ≤ 2 ^ 7) : primeRank 5 (MulAut E) ≤ 1 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply primeRank_le_one_of_square_not_dvd
  obtain ⟨d, hd⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hdim : d ≤ 7 := by
    rw [hd] at hc
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow E d hd]
  interval_cases d <;> norm_num [Fin.prod_univ_succ]

/-- A binary elementary subgroup with an actor of five-rank at least two
and binary action kernel forces ambient two-rank at least eight. -/
theorem eight_le_twoRank_of_elementary_action
    {K : Type*} [Group K] [Finite K] (P W : Subgroup K)
    (he : IsElementaryAbelian 2 W) (hn : P ≤ normalizer (W : Set K))
    (hk : IsPGroup 2 ((centralizer (W : Set K)).subgroupOf P))
    (hr : 2 ≤ primeRank 5 P) : 8 ≤ primeRank 2 K := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let := he
  by_contra! hsmall
  have hc : Nat.card W ≤ 2 ^ 7 :=
    (primeRank_le_iff_elementary_card_le K).mp (by omega) W he
  let f := ModelConjugation.action P W hn (MulEquiv.refl W)
  have hkf : IsPGroup 2 f.ker := by
    rw [ModelConjugation.action_ker]
    exact hk
  have hcop : Nat.Coprime 5 (Nat.card f.ker) := by
    obtain ⟨n,hn⟩ := hkf.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 5 2).pow_right n
  have hlarge := hr.trans (primeRank_le_of_coprime_ker 5 f hcop)
  have hsmall := small_elementary_automorphism_five_rank W hc
  omega

/-- If the ambient two-core is trivial, the same action forces rank at least
eight after quotienting by the center. -/
theorem eight_le_centralQuotient_twoRank_of_elementary_action
    {K : Type*} [Group K] [Finite K] (P W : Subgroup K)
    (he : IsElementaryAbelian 2 W) (hn : P ≤ normalizer (W : Set K))
    (hk : IsPGroup 2 ((centralizer (W : Set K)).subgroupOf P))
    (hr : 2 ≤ primeRank 5 P) (hcore : pCore 2 K = ⊥) :
    8 ≤ primeRank 2 (K ⧸ center K) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply (eight_le_twoRank_of_elementary_action P W he hn hk hr).trans
  apply primeRank_le_of_coprime_ker 2 (QuotientGroup.mk' (center K))
  rw [QuotientGroup.ker_mk']
  exact Nat.prime_two.coprime_iff_not_dvd.mpr
    (PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot hcore (center K) le_rfl)
end Theory.GroupAction
