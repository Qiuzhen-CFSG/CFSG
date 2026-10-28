module
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.SignedThree
public import Theory.GroupTheory.PerfectCubicRank
public import Theory.Alternating.OddCentralCovers
public import Theory.Alternating.PrimeRank
public import Theory.Mathieu.SchurMultipliers.OddLocalPartialInversion
public import Theory.SpecificGroups.PSU3.EvenOddCenterCover
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.SmallOddRanks
/-!
# Small simple quotients in the original nonsemisimple reduction

Odd central covers of A₅, A₆ and A₇ have ordinary odd-prime rank at most
two. At the cubic center the order bound and perfect central Sylow transfer
exclude elementary rank three. The actual M₁₁ and PSU₃(4) multiplier bounds
make their odd central covers centerless, so their proved model ranks apply.

The original section S is quasisimple in the nonsemisimple branch. These
bounds therefore contradict the original A.2.14 ordinary-rank witness,
without assuming that the failure witness was a local-rank failure.
Source: Aschbacher–Smith A.2.12(I), printed p.36.
-/

public section
open Subgroup Theory.GroupTheory PerfectCentralCovering
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.SmallQuotients

private theorem alternating_small_rank (n p : ℕ) (hn : n ≤ 7) (hp : p.Prime) (ho : Odd p) :
    primeRank p (alternatingGroup (Fin n)) ≤ 2 := by
  rw [GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime n p hp (by rintro rfl; norm_num at ho)]
  have h3 : 3 ≤ p := by have := hp.two_le; have := Nat.odd_iff.mp ho; omega
  exact (Nat.div_le_div_right hn).trans ((Nat.div_le_div_left h3 (by decide)).trans (by decide))

theorem alternating_small_odd_cover_rank
    {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
    (n : ℕ) (hn : 5 ≤ n) (hn7 : n ≤ 7)
    (e : L ⧸ center L ≃* alternatingGroup (Fin n))
    (hzodd : Odd (Nat.card (center L))) (p : ℕ) (hp : p.Prime) (ho : Odd p) :
    primeRank p L ≤ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  rcases GLS3.Chapter5.OddCentralCovers.odd_center_alternatives n hn e hzodd with hc | ⟨hn, hc⟩
  · let a := GLS3.Chapter5.OddCentralCovers.alternatingEquivOfCenterCardOne n e hc
    rw [primeRank_equiv p a]
    exact alternating_small_rank n p hn7 hp ho
  · by_cases hp3 : p = 3
    · subst p
      have hzc : IsPGroup 3 (center L) := IsPGroup.of_card (n := 1) (by simpa using hc)
      have hz : center L ≠ ⊥ := by intro hh; simp [hh] at hc
      apply primeRank_le_two_of_center_of_fourth_power_not_dvd hzc hz
      have hg : Nat.card L = 3 * Nat.card (alternatingGroup (Fin n)) := by
        rw [← (center L).card_mul_index, hc, index_eq_card, Nat.card_congr e.toEquiv]
      rw [hg]
      rcases hn with rfl | rfl <;> rw [nat_card_alternatingGroup] <;> norm_num [Nat.factorial]
    · have hcop : Nat.Coprime p (Nat.card (QuotientGroup.mk' (center L)).ker) := by
        rw [QuotientGroup.ker_mk', hc]
        exact (Nat.coprime_primes hp Nat.prime_three).mpr hp3
      rw [primeRank_eq_of_surjective_of_coprime p (QuotientGroup.mk' (center L))
        (QuotientGroup.mk'_surjective _) hcop, primeRank_equiv p e]
      exact alternating_small_rank n p hn7 hp ho

theorem m11_odd_cover_rank
    {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
    (e : L ⧸ center L ≃* Sporadic.Mathieu.M11)
    (hzodd : Odd (Nat.card (center L))) (p : ℕ) (hp : p.Prime) (ho : Odd p) :
    primeRank p L ≤ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  have hzg : IsPGroup 2 (center L) := by
    have hh := Sporadic.Mathieu.SchurMultipliers.PartialInversionSource.m11_cover_kernel_isTwoGroup
      (centralQuotientCover e)
    change IsPGroup 2 (centralQuotientCover e).toMonoidHom.ker at hh
    rwa [centralQuotientCover_ker] at hh
  obtain ⟨k, hk⟩ := hzg.exists_card_eq
  have hk0 : k = 0 := by
    by_contra hh
    exact hzodd.not_two_dvd_nat (hk ▸ dvd_pow_self 2 hh)
  have hzone : Nat.card (center L) = 1 := by simpa [hk0] using hk
  let a : L ≃* Sporadic.Mathieu.M11 :=
    ((QuotientGroup.quotientMulEquivOfEq (card_eq_one.mp hzone)).trans
      QuotientGroup.quotientBot).symm.trans e
  exact Nonsemisimple.RankTwoSieve.m11_primeRank_le_two hp ho a

theorem unitary_four_odd_cover_rank
    {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
    (hm : ClassicalGroup.IsPSU (L ⧸ center L) 3 4)
    (hzodd : Odd (Nat.card (center L))) (p : ℕ) (hp : p.Prime) (ho : Odd p) :
    primeRank p L ≤ 2 := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := hm
  have hd := HermitianForm.EvenOddCenterCover.center_card_dvd J (n := 2) (by decide)
    (by simpa using hcard) (by simpa using hconj) e hzodd
  norm_num at hd
  have hz : center L = ⊥ := hd
  let a : L ≃* L ⧸ center L := ((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).symm
  exact Nonsemisimple.RankTwoSieve.unitary_four_primeRank_le_two hp ho
    ⟨F, inferInstance, inferInstance, J, hcard, hconj, ⟨a.trans e⟩⟩

end CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.SmallQuotients

namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
    [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

theorem CounterexampleToTheoremA.not_small_alternating_centralQuotient
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    (hn : ¬ IsSemisimple G) (n : ℕ) (h5 : 5 ≤ n) (h7 : n ≤ 7)
    (e : S ⧸ center S ≃* alternatingGroup (Fin n)) : False := by
  let := h.section_quasisimple_of_not_semisimple ih.theoremA hn
  have hb := Nonsemisimple.SmallQuotients.alternating_small_odd_cover_rank n h5 h7 e
    (h.section_center_odd_card ih.theoremA) p h.2.2.2.2.1 h.2.2.2.2.2.1
  exact (not_le_of_gt (lemma_A_2_14 h ih.theoremA)) hb

theorem CounterexampleToTheoremA.not_m11_centralQuotient
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    (hn : ¬ IsSemisimple G) (e : S ⧸ center S ≃* Sporadic.Mathieu.M11) : False := by
  let := h.section_quasisimple_of_not_semisimple ih.theoremA hn
  have hb := Nonsemisimple.SmallQuotients.m11_odd_cover_rank e
    (h.section_center_odd_card ih.theoremA) p h.2.2.2.2.1 h.2.2.2.2.2.1
  exact (not_le_of_gt (lemma_A_2_14 h ih.theoremA)) hb

theorem CounterexampleToTheoremA.not_unitary_four_centralQuotient
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    (hn : ¬ IsSemisimple G) (hm : ClassicalGroup.IsPSU (S ⧸ center S) 3 4) : False := by
  let := h.section_quasisimple_of_not_semisimple ih.theoremA hn
  have hb := Nonsemisimple.SmallQuotients.unitary_four_odd_cover_rank hm
    (h.section_center_odd_card ih.theoremA) p h.2.2.2.2.1 h.2.2.2.2.2.1
  exact (not_le_of_gt (lemma_A_2_14 h ih.theoremA)) hb

end CFSG.Quasithin.ChapterA.Section02
