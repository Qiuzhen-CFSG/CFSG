module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalSevenCover
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocalSevenWitness

/-!
# The original Chapter12 seven-point covering alternative

The selected triple A7 quotient is excluded with the original Hall pair
and residual. Thus either seven-point covering alternative now gives the
complete A7 witness and the full conclusion on the original whole reduced
module, together with the actual chosen A5 module. No cubic lift, module
coordinates, or degree-two hypothesis is added.

This closes the two seven-point rows only. The remaining component sieve
and binary-triality ambient exclusion retain their original obligations.
Source: Aschbacher--Smith 5.1.13 and 12.2.2, printed pp.637--638,795,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source Chapter6.Source.RankOneGeneric Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B Y : Subgroup G}
  (a : ChosenModule T L V)
include a

/-- The literal Chapter12 selected container cannot have triple A7 quotient. -/
theorem rankOne_local_cartan_not_seven_cover
    {K : Subgroup G}
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hKC : K ≤ C.map Y.subtype) :
    ¬ IsAlternatingCover (C ⧸ pCore 2 C) 7 := by
  exact LocalSieve.not_alternating_seven_cover
    (a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hK hKT horbit hY hescape C hC hKC

/-- Both seven-point covering rows yield the full original whole-module
and chosen-module conclusions, because the triple cover is impossible. -/
theorem rankOne_local_cartan_seven_covering_exceptional
    {K : Subgroup G}
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hKC : K ≤ C.map Y.subtype)
    (hm : IsAlternating (C ⧸ pCore 2 C) 7 ∨ IsAlternatingCover (C ⧸ pCore 2 C) 7) :
    CartanExceptionalConclusion T L (RankOneModule.wholeReduced T L) H ∧
      RankOneModule.ExceptionalExit T L H ∧ n = 2 ∧
      IsConjugationModel L V a5Module := by
  apply a.rankOne_local_cartan_seven_exceptional h hmany hn hpsl hH hgen c
    hK hKT horbit hY hescape C hC hKC
  exact hm.resolve_right (a.rankOne_local_cartan_not_seven_cover h hmany hn hpsl
    hH hgen c hK hKT horbit hY hescape C hC hKC)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
