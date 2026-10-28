module
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.Catalogue

/-!
# The remaining Fi₂₄ source model without a numerical rank premise

Every full-catalogue branch except Fi₂₄ is excluded by the established
ordinary two-rank bounds and the original source endgame. Thus an original
nonsemisimple counterexample has the literal Fi₂₄ central quotient. The
source owner can now use its actual involution-centralizer datum, already
needed elsewhere, instead of constructing a separate numerical rank witness.

This preserves the numerical conditional theorem in `Catalogue`; the new
reduction takes only the original counterexample and proper-section induction.
Source: Aschbacher–Smith A.2.12, printed pp.35–36.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
universe u
variable {Q : Type u} [Group Q] [Finite Q] [Nontrivial Q]
/-- All twenty-six actual carriers reduce to M₁₁ or the final Fi₂₄ source branch. -/
theorem sporadic_models_or_fi24 (hr : primeRank 2 Q ≤ 2)
    (hm : KnownSimple.IsSporadicCarrier Q) :
    Nonempty (Q ≃* Sporadic.Mathieu.M11) ∨ Nonempty (Q ≃* Sporadic.Fischer.Fi24Prime.Carrier) := by
  obtain ⟨name,⟨a⟩⟩ := hm
  cases name with
  | m11 => exact Or.inl ⟨a⟩
  | m12 => exact (no_mathieu_janko_one_model hr .m12 (by simp) a).elim
  | m22 => exact (no_mathieu_janko_one_model hr .m22 (by simp) a).elim
  | m23 => exact (no_mathieu_janko_one_model hr .m23 (by simp) a).elim
  | m24 => exact (no_mathieu_janko_one_model hr .m24 (by simp) a).elim
  | j1 => exact (no_mathieu_janko_one_model hr .j1 (by simp) a).elim
  | j2 => exact (no_three_permutation_models hr .j2 (by simp) a).elim
  | mcl => exact (no_three_permutation_models hr .mcl (by simp) a).elim
  | co3 => exact (no_three_permutation_models hr .co3 (by simp) a).elim
  | j4 => exact (no_janko_four_held_model hr .j4 (by simp) a).elim
  | he => exact (no_janko_four_held_model hr .he (by simp) a).elim
  | hs => exact (no_higman_sims_rudvalis_model hr .hs (by simp) a).elim
  | ru => exact (no_higman_sims_rudvalis_model hr .ru (by simp) a).elim
  | hn => exact (no_three_large_sporadic_models hr .hn (by simp) a).elim
  | babyMonster => exact (no_three_large_sporadic_models hr .babyMonster (by simp) a).elim
  | monster => exact (no_three_large_sporadic_models hr .monster (by simp) a).elim
  | j3 => exact (no_janko_three_model hr a).elim
  | suz => exact (no_suzuki_sporadic_model hr a).elim
  | onan => exact (no_onan_model hr a).elim
  | co1 => exact (no_conway_one_model hr a).elim
  | co2 => exact (no_conway_two_model hr a).elim
  | fi22 => exact (no_fischer_twenty_two_model hr a).elim
  | fi23 => exact (no_fischer_twenty_three_model hr a).elim
  | th => exact (no_thompson_model hr a).elim
  | ly => exact (no_lyons_model hr a).elim
  | fi24Prime => exact Or.inr ⟨a⟩
end CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02
open Nonsemisimple.RankTwoSieve
universe u
variable {G S : Type u} [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

theorem CounterexampleToTheoremA.centralQuotient_fi24_of_not_semisimple
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hn : ¬ IsSemisimple G) :
    Nonempty ((S ⧸ center S) ≃* Sporadic.Fischer.Fi24Prime.Carrier) := by
  let := h.2.2.2.1.isPerfect
  let := h.section_centralQuotient_simple_of_not_semisimple ih.theoremA hn
  have hr := h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih.theoremA hn
  have hm := h.section_centralQuotient_knownCarrier_of_not_semisimple ih.theoremA hn
  have hf (hf : False) : Nonempty ((S ⧸ center S) ≃* Sporadic.Fischer.Fi24Prime.Carrier) := hf.elim
  cases hm with
  | cyclic hm => exact hf (no_prime_cyclic_model hm)
  | alternating n hp a =>
    apply hf
    apply h.rankTwoSurvivors_false ih hn
    rcases alternating_source_models hr hp a.some with ha | hb
    · exact Or.inl ha
    · exact Or.inr (Or.inr (Or.inr (Or.inl hb)))
  | classical hm =>
    apply hf
    apply h.rankTwoSurvivors_false ih hn
    rcases classical_source_models hr hm with ha | hb | hc | hd
    · exact Or.inl ha
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr (Or.inl hc))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hd))))
  | g2 hm => exact hf (not_g2_carrier hr hm)
  | suzuki m hp a => exact hf (no_suzuki_model hr m hp a.some)
  | exceptional hm =>
    apply hf
    cases hm with
    | f4 q hm => exact no_f4_model hr hm
    | e6 q hm => exact no_e6_model hr hm
    | e7 q hm => exact no_e7_model hr hm
    | e8 q hm => exact no_e8_model hr hm
    | twistedE6 q hm => exact no_twisted_e6_model hr hm
    | reeG2 q hm => exact no_reeG2_model hr hm
  | triality hm =>
    apply hf
    obtain ⟨P,⟨a⟩⟩ := hm
    by_cases hp : P.prime=2
    · apply no_binary_triality_model hr P.exponent P.exponent_pos
      exact ⟨P,by change P.prime ^ P.exponent = 2^P.exponent; rw [hp],⟨a⟩⟩
    · exact h.centralQuotient_no_odd_triality ih P (P.prime_prime.odd_of_ne_two hp) a
  | reeF4 hm => exact hf (no_reeF4_model hr hm)
  | smallDerived hm =>
    apply hf
    apply h.rankTwoSurvivors_false ih hn
    rcases smallDerived_source_models hr hm with ha | hb
    · exact Or.inl ha
    · exact Or.inr (Or.inr (Or.inl hb))
  | sporadic hm =>
    rcases sporadic_models_or_fi24 hr hm with hm11 | hfi
    · exact hf (h.rankTwoSurvivors_false ih hn
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm11))))))
    · exact hfi

/-- The final source owner may discharge the remaining actual Fi₂₄ model directly. -/
theorem CounterexampleToTheoremA.rankTwoCatalogue_false_of_fi24_exclusion
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hn : ¬ IsSemisimple G)
    (hfi : ∀ _e : (S ⧸ center S) ≃* Sporadic.Fischer.Fi24Prime.Carrier, False) : False :=
  hfi (h.centralQuotient_fi24_of_not_semisimple ih hn).some
end CFSG.Quasithin.ChapterA.Section02
