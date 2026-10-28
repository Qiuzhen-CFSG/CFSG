module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalA7Exclusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocalModule

/-!
# The original local Cartan omega-centralization in Chapter 12

The completed block contradiction excludes the maximal A₇ configuration
produced by the earlier FF reduction. Hence the actual witnessed component
centralizes the original Sylow omega-center. At degree two this also gives
the complete original moved module and, through the original relocation
sieve, the exceptional conclusion. The general postcentralization degree
argument and the sieve itself remain obligations of the universal source.

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

/-- The original component witness centralizes the original omega-center,
with the FF and both block arguments discharged. -/
theorem rankOne_local_cartan_centralizes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X C) : X ≤ omegaCentralizer T :=
  localCartan_centralizes
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c hY d

/-- At degree two, omega-centralization and recognition of the whole
original commutator are both consequences of the witnessed source inputs. -/
theorem rankOne_local_cartan_centralization_degree_two
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ 2))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X C) :
    X ≤ omegaCentralizer T ∧ Chapter6.Source.IsOneOrTwoA5Modules L (RankOneModule.commutatorLayer T L) :=
  localCartan_centralization_degree_two
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany (by decide) hpsl) hH hgen c hY d

/-- The literal changed-choice consumer at degree two retains only the
source sieve, with the A7 contradiction and module recognition discharged. -/
theorem rankOne_local_cartan_escape_of_sieve_degree_two
    (hsieve : LocalCartanSieve KnownSimple.IsKnownSimple G)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ 2))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    CartanExceptionalConclusion T L (RankOneModule.wholeReduced T L) H ∧
      RankOneModule.ExceptionalExit T L H ∧
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module :=
  D.rankOne_exceptional_local_cartan_of_sieve_a7_degree_two
    h hmany hpsl hH hgen c hY hescape hsieve localCartan_a7Exclusion
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
