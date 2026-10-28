module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalMinusTorus
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalNaturalExclusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocalRelocation

/-!
# The postcentralization Cartan degree argument in Chapter 12

The witnessed cubic excludes a natural action on the full reduced subgroup
and the full moved layer. An actual minus torus in the omega-centralizer,
containing that cubic and inverted modulo T from the original component, forces n=2
by the A₇/J₂/M₂₃ carrier calculations. The existing whole-module recognition
and relocation then give the original exceptional exit and chosen marking.

The original universal inputs and both Hall conditions are unchanged.
Constructing the minus torus from the remaining module alternatives and
constructing the initial component-and-cubic witness remain source obligations.
Source: Aschbacher–Smith 5.1.13, printed p.638, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B Y X C E : Subgroup G}
  (D : ChosenModule T L V)
include D

/-- The whole original reduced action and moved layer have no natural marking. -/
theorem rankOne_local_cartan_not_natural
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n m : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X C) :
    (¬ Chapter6.Source.IsNaturalModule L (RankOneModule.wholeReduced T L) m) ∧
      (¬ Chapter6.Source.IsNaturalModule L (RankOneModule.commutatorLayer T L) m) :=
  localCartan_not_natural
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c hY d

/-- In particular the doubled-natural row of 5.1.3 is excluded without
assuming invariance of the individual summands. -/
theorem rankOne_local_cartan_not_repeated_natural
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X C)
    (F : ChapterB.QuasisimpleSource.BinaryField) (k : ℕ) :
    (¬ Chapter6.Source.IsConjugationModel L (RankOneModule.wholeReduced T L)
      (ChapterB.QuasisimpleSource.repeated (ChapterB.QuasisimpleSource.linearNatural F 2) k)) ∧
    (¬ Chapter6.Source.IsConjugationModel L (RankOneModule.commutatorLayer T L)
      (ChapterB.QuasisimpleSource.repeated (ChapterB.QuasisimpleSource.linearNatural F 2) k)) :=
  localCartan_not_repeated_natural
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c hY d F k

/-- The actual minus torus completes the degree, full layer, component and
chosen-module conclusions under the original Chapter12 inputs. -/
theorem rankOne_local_cartan_escape_of_minus_torus
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X C)
    (hEA : E ≤ A) (hCE : C ≤ E) (hEC : E ≤ omegaCentralizer T)
    (hcard : Nat.card E = 2 ^ (n / 2) + 1)
    (hinv : ∃ t ∈ (T : Subgroup G) ⊓ X, ∀ e ∈ E, t*e*t⁻¹*e ∈ (T : Subgroup G)) :
    n = 2 ∧ CartanExceptionalConclusion T L (RankOneModule.wholeReduced T L) H ∧
      RankOneModule.ExceptionalExit T L H ∧
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module := by
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  have he := localCartan_degree_two_of_minus_torus hi hH hgen c hY d hEA hCE hEC hcard hinv
  have hc := localCartan_escape_of_minus_torus hi hH hgen c hY d hEA hCE hEC hcard hinv
  have hx := RankOneModule.exceptional_of_cartan_conclusion hc
  exact ⟨he,hc,hx,(D.rankOne_exceptional_module_and_exponent hn hpsl hx).2⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
