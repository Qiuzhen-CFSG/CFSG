module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalMinusInversion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocalMinusTorus

/-!
# The original inverter and minus torus in Chapter 12

Construct the actual minus torus in the original Hall subgroup and prove
its inversion modulo the original Sylow from the witnessed cubic inverter.
There is no assumed normalization of the selected Hall complement by
that inverter. At odd half-degree the cubic lies in this same torus.

The remaining module premise is that these minus-torus roots centralize
the original omega-center. With that premise the three concrete exceptional
quotient spectra force degree two and give the whole-layer and chosen-module
conclusions. Constructing the initial witness, odd half-degree, and this
centralization from the original source conditions remain open.
Source: Aschbacher--Smith 5.1.13, final paragraph, printed p.638,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B Y X C : Subgroup G}
  (D : ChosenModule T L V)
include D

/-- Construct the literal minus torus and its actual original inverter. -/
theorem rankOne_local_cartan_exists_inverted_minus_torus
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X C) (hm : Odd (n/2)) :
    ∃ E : Subgroup G, E ≤ A ∧ C ≤ E ∧ Nat.card E = 2^(n/2)+1 ∧
      (∀ x : G, x ∈ E ↔ x ∈ A ∧ x^(2^(n/2)+1) = 1) ∧
      ∃ t ∈ (T : Subgroup G) ⊓ X,
        ∀ x ∈ E, t*x*t⁻¹*x ∈ (T : Subgroup G) :=
  d.exists_inverted_minus_torus
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) c hm

/-- The degree and full exceptional exit use only the remaining odd
half-degree and minus-root fixation premises from the source module argument. -/
theorem rankOne_local_cartan_escape_of_minus_roots_centralize
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X C) (hm : Odd (n/2))
    (hc : ∀ x ∈ A, x^(2^(n/2)+1) = 1 → x ∈ omegaCentralizer T) :
    n = 2 ∧ CartanExceptionalConclusion T L (RankOneModule.wholeReduced T L) H ∧
      RankOneModule.ExceptionalExit T L H ∧
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module := by
  obtain ⟨he,hout⟩ := localCartan_escape_of_minus_roots_centralize
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c hY d hm hc
  have hx := RankOneModule.exceptional_of_cartan_conclusion hout
  exact ⟨he,hout,hx,(D.rankOne_exceptional_module_and_exponent hn hpsl hx).2⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
