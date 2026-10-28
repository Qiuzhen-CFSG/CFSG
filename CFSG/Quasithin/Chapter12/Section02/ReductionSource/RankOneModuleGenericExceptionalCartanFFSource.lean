module

public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FFReduction.SourceApplications
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# The FF source configuration on the original Chapter 12 module

The proven FF construction is supplied to the existing local Cartan relocation
on the whole reduced subgroup. The chosen module, actual exceptional exit and
exponent conclusion are unchanged. The Baumann theorem is supplied by its
original-input proof; only the independently owned sieve, A₇ exclusion and
module-recognition source steps remain explicit in the final application.

Source: Aschbacher--Smith, 5.1.13 and 12.2.2, pp.637--638,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The actual local Chapter 12 consumer with its FF premise proved. -/
theorem rankOne_exceptional_local_cartan_of_ff_source
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    {A B Y : Subgroup G} (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (hbaum : RankOneBaumannNormalizerControl G)
    (hsieve : LocalCartanSieve KnownSimple.IsKnownSimple G)
    (ha7 : LocalCartanA7Exclusion G) (hm : LocalCartanModuleRecognition G) :
    CartanExceptionalConclusion T L (RankOneModule.wholeReduced T L) H ∧
      RankOneModule.ExceptionalExit T L H ∧ n = 2 ∧
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module :=
  D.rankOne_exceptional_local_cartan_of_source h hmany hn hpsl hH hgen c hY hescape
    hsieve (localCartanCentralization_of_baumann_and_source_steps hbaum ha7 hm)

/-- The actual Chapter 12 application with both the FF construction and its
earlier Baumann normalizer premise discharged on the original whole module. -/
theorem rankOne_exceptional_local_cartan_of_sieve_a7_and_recognition
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    {A B Y : Subgroup G} (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (hsieve : LocalCartanSieve KnownSimple.IsKnownSimple G)
    (ha7 : LocalCartanA7Exclusion G) (hm : LocalCartanModuleRecognition G) :
    CartanExceptionalConclusion T L (RankOneModule.wholeReduced T L) H ∧
      RankOneModule.ExceptionalExit T L H ∧ n = 2 ∧
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module :=
  D.rankOne_exceptional_local_cartan_of_source h hmany hn hpsl hH hgen c hY hescape
    hsieve (localCartanCentralization_of_a7_and_recognition ha7 hm)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
