module
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.Classical
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.Sporadic
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.Cyclic
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.F4
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.SplitExceptional
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.TwistedE6
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.OddTriality
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoEndgame

/-!
# Exhausting the full known-simple catalogue in the nonsemisimple source case

Every constructor of the full catalogue is handled on the actual S/Z(S).
The classical, alternating, small-derived and M₁₁ survivors feed the original
counterexample endgame, which retains both rank clauses and the central
p-kernel argument. Odd triality is excluded directly by its actual proper
SL₂(q³) section and the original induction hypothesis. All other entries
have concrete elementary-eight obstructions.

The only independently supplied model fact is the literal Fi₂₄ two-rank
certificate. No catalogue reduction, quotient quasithinness, local-rank
failure or prime-core identity is taken as an input.
Source: Aschbacher–Smith A.2.12, printed pp.35–36.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02
open Nonsemisimple.RankTwoSieve
universe u
variable {G S : Type u} [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

theorem CounterexampleToTheoremA.rankTwoCatalogue_false_of_fi24_rank
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hn : ¬ IsSemisimple G)
    (hfi : 3 ≤ primeRank 2 Sporadic.Fischer.Fi24Prime.Carrier) : False := by
  let := h.2.2.2.1.isPerfect
  let := h.section_centralQuotient_simple_of_not_semisimple ih.theoremA hn
  have hr := h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih.theoremA hn
  have hm := h.section_centralQuotient_knownCarrier_of_not_semisimple ih.theoremA hn
  cases hm with
  | cyclic hm => exact no_prime_cyclic_model hm
  | alternating n hp a =>
    apply h.rankTwoSurvivors_false ih hn
    rcases alternating_source_models hr hp a.some with ha | hb
    · exact Or.inl ha
    · exact Or.inr (Or.inr (Or.inr (Or.inl hb)))
  | classical hm =>
    apply h.rankTwoSurvivors_false ih hn
    rcases classical_source_models hr hm with ha | hb | hc | hd
    · exact Or.inl ha
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr (Or.inl hc))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hd))))
  | g2 hm => exact not_g2_carrier hr hm
  | suzuki m hp a => exact no_suzuki_model hr m hp a.some
  | exceptional hm =>
    cases hm with
    | f4 q hm => exact no_f4_model hr hm
    | e6 q hm => exact no_e6_model hr hm
    | e7 q hm => exact no_e7_model hr hm
    | e8 q hm => exact no_e8_model hr hm
    | twistedE6 q hm => exact no_twisted_e6_model hr hm
    | reeG2 q hm => exact no_reeG2_model hr hm
  | triality hm =>
    obtain ⟨P,⟨a⟩⟩ := hm
    by_cases hp : P.prime=2
    · apply no_binary_triality_model hr P.exponent P.exponent_pos
      exact ⟨P,by change P.prime ^ P.exponent = 2^P.exponent; rw [hp],⟨a⟩⟩
    · exact h.centralQuotient_no_odd_triality ih P (P.prime_prime.odd_of_ne_two hp) a
  | reeF4 hm => exact no_reeF4_model hr hm
  | smallDerived hm =>
    apply h.rankTwoSurvivors_false ih hn
    rcases smallDerived_source_models hr hm with ha | hb
    · exact Or.inl ha
    · exact Or.inr (Or.inr (Or.inl hb))
  | sporadic hm =>
    apply h.rankTwoSurvivors_false ih hn
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (sporadic_model_of_twoRank_le_two hr hfi hm)))))
end CFSG.Quasithin.ChapterA.Section02
