module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalRelocation
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocalA7Exclusion

/-!
# Relocating the original Chapter 12 Cartan witness

The original witness enlarges to a maximal local component normal in the
whole Sylow omega-centralizer. Its quotient is genuinely A₇, J₂ or M₂₃,
and it retains the same escaping cubic and inverter. The normalizer of
omega and every nonidentity omega-point centralizer normalize this same
component. No second invocation of the component sieve is needed.

At degree two the existing whole-module recognition supplies the literal
exceptional exit and the original chosen-module marking. The universal
degree argument and the construction of the first witness remain open.
Source: Aschbacher–Smith 5.1.13, printed pp.637–638, refs/quasithin.pdf.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B Y X C : Subgroup G}
  (D : ChosenModule T L V)
include D

/-- The literal source witness gives one maximal component in the whole
omega-centralizer, with its full normalizer and point-centralizer bounds. -/
theorem rankOne_local_cartan_centralizer_witness
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X C) :
    ∃ K : Subgroup G, X ≤ K ∧ K ∈ Chapter1.LStar G (T : Subgroup G) ∧
      LocalCartanWitness T H A (omegaCentralizer T) K C ∧
      normalizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤
        normalizer (K : Set G) ∧
      (∀ z ∈ omegaOneCenterAmbient (T : Subgroup G), z ≠ 1 →
        centralizer ({z} : Set G) ≤ normalizer (K : Set G)) :=
  localCartan_centralizer_witness
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c hY d

/-- A single original witness at degree two supplies the whole exceptional
conclusion and chosen-module marking, without a universal sieve premise. -/
theorem rankOne_local_cartan_escape_of_witness_degree_two
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ 2))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X C) :
    CartanExceptionalConclusion T L (RankOneModule.wholeReduced T L) H ∧
      RankOneModule.ExceptionalExit T L H ∧
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module := by
  have he := localCartan_escape_of_witness_degree_two
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany (by decide) hpsl) hH hgen c hY d
  have hx := RankOneModule.exceptional_of_cartan_conclusion he
  exact ⟨he,hx,(D.rankOne_exceptional_module_and_exponent (by decide : 1 < 2) hpsl hx).2⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
