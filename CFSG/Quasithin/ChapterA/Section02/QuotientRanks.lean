module

public import CFSG.Quasithin.ChapterA.Section02.OddPrimeRank
public import Theory.Quasithin.LocalRank
public import Theory.GroupTheory.TwoLocalSurjective

/-!
# Low-rank quotient inequalities

Aschbacher–Smith, *The Classification of Quasithin Groups*, combined manuscript
(1 March 2004), Lemma A.2.7, printed p. 34 (`refs/quasithin.pdf`).

At an odd prime, rank at most one forces cyclic Sylow subgroups, so rank cannot
increase in a quotient of such a group. Splitting on the source rank gives the
same inequality whenever the target rank is at most two. For the local versions,
the Frattini argument lifts every target two-local to a source two-local with a
surjective restriction. Apply the ordinary inequalities to these restrictions
and take the supremum. Finally local prime rank is bounded by ordinary prime
rank, which gives the simultaneous assertion (5).
-/

public section

namespace TwoLocalPrimeRank

variable {G H : Type*} [Group G] [Finite G] [Group H]
    {p : ℕ} [Fact p.Prime]

/-- Local odd-prime rank cannot increase in a surjective image of local rank at most one. -/
theorem le_of_surjective_of_source_le_one
    (hpodd : p ≠ 2) (f : G →* H) (hf : Function.Surjective f)
    (hrank : twoLocalPrimeRank p G ≤ 1) :
    twoLocalPrimeRank p H ≤ twoLocalPrimeRank p G := by
  let : Finite H := Finite.of_surjective f hf
  apply (twoLocalPrimeRank_le_iff p _).mpr
  intro M hM
  obtain ⟨L, hL, _, φ, hφ, _⟩ := hM.exists_surjective_of_surjective f hf
  exact (PrimeRank.le_of_surjective_of_source_le_one hpodd φ hφ
    ((hL.primeRank_le p).trans hrank)).trans (hL.primeRank_le p)

/-- Local odd-prime rank cannot increase in a surjective image of local rank at most two. -/
theorem le_of_surjective_of_target_le_two
    (hpodd : p ≠ 2) (f : G →* H) (hf : Function.Surjective f)
    (hrank : twoLocalPrimeRank p H ≤ 2) :
    twoLocalPrimeRank p H ≤ twoLocalPrimeRank p G := by
  let : Finite H := Finite.of_surjective f hf
  apply (twoLocalPrimeRank_le_iff p _).mpr
  intro M hM
  obtain ⟨L, hL, _, φ, hφ, _⟩ := hM.exists_surjective_of_surjective f hf
  exact (PrimeRank.le_of_surjective_of_target_le_two hpodd φ hφ
    ((hM.primeRank_le p).trans hrank)).trans (hL.primeRank_le p)

end TwoLocalPrimeRank

namespace CFSG.Quasithin.ChapterA.Section02

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A.2.7(1): ordinary rank does not increase when the source rank is at most one. -/
theorem lemma_A_2_7_1 (K : Subgroup G) [K.Normal] (hpodd : p ≠ 2)
    (hrank : primeRank p G ≤ 1) : primeRank p (G ⧸ K) ≤ primeRank p G :=
  PrimeRank.le_of_surjective_of_source_le_one hpodd
    (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K) hrank

/-- A.2.7(2): local rank does not increase when the source local rank is at most one. -/
theorem lemma_A_2_7_2 (K : Subgroup G) [K.Normal] (hpodd : p ≠ 2)
    (hrank : twoLocalPrimeRank p G ≤ 1) :
    twoLocalPrimeRank p (G ⧸ K) ≤ twoLocalPrimeRank p G :=
  TwoLocalPrimeRank.le_of_surjective_of_source_le_one hpodd
    (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K) hrank

/-- A.2.7(3): ordinary rank does not increase when the quotient rank is at most two. -/
theorem lemma_A_2_7_3 (K : Subgroup G) [K.Normal] (hpodd : p ≠ 2)
    (hrank : primeRank p (G ⧸ K) ≤ 2) : primeRank p (G ⧸ K) ≤ primeRank p G :=
  PrimeRank.le_of_surjective_of_target_le_two hpodd
    (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K) hrank

/-- A.2.7(4): local rank does not increase when the quotient local rank is at most two. -/
theorem lemma_A_2_7_4 (K : Subgroup G) [K.Normal] (hpodd : p ≠ 2)
    (hrank : twoLocalPrimeRank p (G ⧸ K) ≤ 2) :
    twoLocalPrimeRank p (G ⧸ K) ≤ twoLocalPrimeRank p G :=
  TwoLocalPrimeRank.le_of_surjective_of_target_le_two hpodd
    (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K) hrank

/-- A.2.7(5): a quotient of ordinary rank at most two satisfies both rank inequalities. -/
theorem lemma_A_2_7_5 (K : Subgroup G) [K.Normal] (hpodd : p ≠ 2)
    (hrank : primeRank p (G ⧸ K) ≤ 2) :
    primeRank p (G ⧸ K) ≤ primeRank p G ∧
      twoLocalPrimeRank p (G ⧸ K) ≤ twoLocalPrimeRank p G :=
  ⟨lemma_A_2_7_3 K hpodd hrank,
    lemma_A_2_7_4 K hpodd ((twoLocalPrimeRank_le_primeRank p).trans hrank)⟩

end CFSG.Quasithin.ChapterA.Section02
