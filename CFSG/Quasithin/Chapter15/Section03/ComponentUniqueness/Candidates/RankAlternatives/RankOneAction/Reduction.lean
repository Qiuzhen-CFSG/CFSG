module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.RankOneAction.Local
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.RankOneAction.Parameters
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels

/-!
# The established parameter and Borel reductions in 15.3.37

The source local hypotheses give a proper Sylow-two overgroup in the
component, of order divisible by three. The concrete model lemmas restrict
the PSL₂ exponent and the Fermat--Mersenne parameter, with actual exceptional
isomorphisms. The unitary congruence forces its exponent to be even.
The only unresolved parameter case is PSL₃(2ⁿ), n > 1, with 2ⁿ ≡ -1 mod 3.

The Borel identification below is conditional on its characteristic-two
property; `BorelGeometry` discharges that premise from the concrete models.
This is a reduction, not a completed proof of the source rank-one branch.
Source: Aschbacher--Smith, 15.3.37, printed p.1135.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.RankOneAction
variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L : Subgroup G} (h : Setup Yplus S M I L)

include h in
theorem Setup.intersection_sylow_overgroup : ∃ P : Sylow 2 L,
    (P : Subgroup L) ≤ M.subgroupOf L ∧ M.subgroupOf L < ⊤ := by
  obtain ⟨P, hP⟩ := h.component_sylow
  refine ⟨P, ?_, lt_top_iff_ne_top.mpr ?_⟩
  · intro x hx
    exact h.sylow_le ((hP ▸ mem_map_of_mem L.subtype hx).1)
  · intro he
    apply h.component_outside
    intro x hx
    exact show (⟨x, hx⟩ : L) ∈ M.subgroupOf L from he ▸ mem_top _

include h in
theorem Setup.binary_exponent_even {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL L 2 (2 ^ n)) : Even n := by
  obtain ⟨P, hPD, hD⟩ := h.intersection_sylow_overgroup
  exact RankOneAction.binary_exponent_even hn hm P _ hPD hD h.three_dvd_intersection

include h in
theorem Setup.fermatMersenne_parameter {p : ℕ}
    (hp : IsFermatOrMersennePrime p) (hm : ClassicalGroup.IsPSL L 2 p) :
    p = 5 ∨ p = 7 := by
  obtain ⟨P, hPD, hD⟩ := h.intersection_sylow_overgroup
  exact RankOneAction.fermatMersenne_parameter hp hm h.component_nonsolvable P _ hPD hD
    h.three_dvd_intersection

include h in
theorem Setup.fermatMersenne_model {p : ℕ}
    (hp : IsFermatOrMersennePrime p) (hm : ClassicalGroup.IsPSL L 2 p) :
    RankOneModel L := by
  rcases h.fermatMersenne_parameter hp hm with rfl | rfl
  · exact rankOneModel_of_prime_five hm
  · exact rankOneModel_of_prime_seven hm

include h in
theorem Setup.rankOne_borel_facts (hm : ChapterF.Source.IsRankOneModel L) :
    ChapterF.Source.RankOneBorelFacts L S := by
  obtain ⟨P, hP⟩ := h.component_sylow
  exact ChapterF.Source.rankOneBorelFacts_of_sylow L S P hP (hm.rankOneSylowFacts P)

include h in
theorem Setup.rankOne_borel_identification (hm : ChapterF.Source.IsRankOneModel L)
    (hchar : generalizedFitting (ChapterF.Source.borel L S) =
      pCore 2 (ChapterF.Source.borel L S)) :
    ChapterF.Source.borel L S = M ⊓ L ∧
      Yplus ⊔ S ≤ normalizer (ChapterF.Source.borel L S : Set G) ∧
      ChapterF.Source.borel L S ≤ normalizer (Yplus : Set G) := by
  have hb := h.rankOne_borel_facts hm
  exact ⟨h.borel_eq_intersection hb hchar, h.borel_invariant hb,
    h.borel_normalizes_yplus hb hchar⟩

include h in
theorem Setup.rankOneModel_or_linear_three (hm : RankOneInitialModel L) :
    RankOneModel L ∨ ∃ n : ℕ, 1 < n ∧ 2 ^ n % 3 = 2 ∧
      ClassicalGroup.IsPSL L 3 (2 ^ n) := by
  rcases hm with ⟨n, hn, hm⟩ | ⟨n, hn, hmod, hm⟩ |
    ⟨n, hn, hmod, hm⟩ | ⟨p, hp, hm⟩
  · exact Or.inl (Or.inl ⟨n, hn, h.binary_exponent_even hn hm, hm⟩)
  · by_cases he : n = 1
    · subst n
      exact Or.inl (Or.inr (Or.inr (by simpa using hm)))
    · exact Or.inr ⟨n, by omega, hmod, hm⟩
  · exact Or.inl (Or.inr (Or.inl ⟨n, hn,
      (even_iff_two_pow_mod_three n).mpr hmod, hm⟩))
  · exact Or.inl (h.fermatMersenne_model hp hm)

end CFSG.Quasithin.Chapter15.Section03.Candidates.RankOneAction
