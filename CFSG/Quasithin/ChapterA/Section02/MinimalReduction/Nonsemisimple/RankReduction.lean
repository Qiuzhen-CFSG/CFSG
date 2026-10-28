module

public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.CoreAction
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.NoSL2Image
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.PrimeCore.CoreRanks
public import Theory.GroupTheory.GeneralizedFitting.PerfectCentralSemisimple

/-!
# The nonsemisimple source branch has two-rank at most two

If every odd prime core has rank at most two, any noncentral core gives a
prime-field SL₂ quotient by the supercritical action theorem. The original
semisimple covering excludes such a quotient. Hence the Fitting subgroup
is central, and perfect central covering lifts semisimplicity to G.
Otherwise A.1.28 and the actual trivial Z-star quotient bound the two-rank
by two. This argument uses no quasithin inheritance to an odd-core quotient.

Source: Aschbacher–Smith A.2.12, printed pp.35–36. The subsequent known-simple
two-rank-two inspection and proper SL₂ section contradiction remain necessary.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
    [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

theorem CounterexampleToTheoremA.primeCore_le_center_of_rank_le_two
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    {q : ℕ} [Fact q.Prime] (hq : Odd q) (hr : primeRank q (pCore q G) ≤ 2) :
    pCore q G ≤ center G := by
  let := h.isPerfect ih
  by_contra hn
  obtain ⟨hq3, ⟨f, hf⟩ | ⟨_, f, hf⟩⟩ := perfect_core_action_models hq hr hn
  · exact h.not_surjective_SL2 ih hq3 f hf
  · let : Fact (Nat.Prime 5) := ⟨by decide⟩
    exact h.not_surjective_SL2 ih (by decide : 3 < 5) f hf

theorem CounterexampleToTheoremA.isSemisimple_of_odd_primeCore_ranks
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hr : ∀ (q : ℕ) [Fact q.Prime], Odd q → primeRank q (pCore q G) ≤ 2) :
    IsSemisimple G := by
  have hF : fittingSubgroup G ≤ center G := by
    rw [fitting_eq_sup_pCore]
    apply iSup_le
    intro q
    have hp : q.val.val.Prime := Nat.prime_of_mem_primeFactors q.val.property
    let : Fact q.val.val.Prime := ⟨hp⟩
    by_cases hq : q.val.val = 2
    · rw [hq, lemma_A_2_10 h ih]
      exact bot_le
    · exact h.primeCore_le_center_of_rank_le_two ih (hp.odd_of_ne_two hq)
        (hr _ (hp.odd_of_ne_two hq))
  obtain ⟨f, hf⟩ := h.exists_surjective ih
  have hk : f.ker ≤ center G := by
    apply le_trans _ hF
    rw [← h.center_preimage_eq_fitting ih f hf]
    intro x hx
    change f x ∈ center S
    rw [show f x = 1 from hx]
    exact one_mem _
  let c : PerfectCentralCovering.Cover G S :=
    { toMonoidHom := f, surjective := hf,
      isPerfect := h.isPerfect ih, ker_le_center := hk }
  exact c.semisimple h.2.2.2.1

/-- The genuine two-rank conclusion entering the remaining catalogue sieve.
Neither prime-core identification nor a quotient-quasithinness premise is needed. -/
theorem CounterexampleToTheoremA.twoRank_le_two_of_not_semisimple
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G) : primeRank 2 G ≤ 2 := by
  by_contra hr
  apply hn
  apply h.isSemisimple_of_odd_primeCore_ranks ih
  intro q _ hq
  exact h.primeCore_rank_le_two_of_three_le_twoRank ih hq (by omega)

theorem CounterexampleToTheoremA.section_twoRank_eq
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G) :
    primeRank 2 S = primeRank 2 G := by
  obtain ⟨f, hf⟩ := h.exists_surjective ih
  have hk : f.ker ≤ (center S).comap f := by
    intro x hx
    change f x ∈ center S
    rw [show f x = 1 from hx]
    exact one_mem _
  have hc : Nat.Coprime 2 (Nat.card f.ker) :=
    (Nat.coprime_two_left.mpr (h.center_preimage_odd_card ih f hf)).of_dvd_right
      (card_dvd_of_le hk)
  exact (primeRank_eq_of_surjective_of_coprime 2 f hf hc).symm

theorem CounterexampleToTheoremA.section_centralQuotient_twoRank_eq
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G) :
    primeRank 2 (S ⧸ center S) = primeRank 2 G := by
  have hc : Nat.Coprime 2 (Nat.card (QuotientGroup.mk' (center S)).ker) := by
    rw [QuotientGroup.ker_mk']
    exact Nat.coprime_two_left.mpr (h.section_center_odd_card ih)
  exact (primeRank_eq_of_surjective_of_coprime 2 (QuotientGroup.mk' (center S))
    (QuotientGroup.mk'_surjective _) hc).symm.trans (h.section_twoRank_eq ih)

theorem CounterexampleToTheoremA.section_centralQuotient_twoRank_le_two_of_not_semisimple
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G) : primeRank 2 (S ⧸ center S) ≤ 2 := by
  rw [h.section_centralQuotient_twoRank_eq ih]
  exact h.twoRank_le_two_of_not_semisimple ih hn

end CFSG.Quasithin.ChapterA.Section02
