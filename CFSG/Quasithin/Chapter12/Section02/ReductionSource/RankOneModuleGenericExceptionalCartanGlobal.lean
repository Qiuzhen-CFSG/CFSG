module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobal
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartan

/-!
# The small-Cartan reduction on the original Chapter 12 setup

The whole reduced subgroup supplies the unchanged generic source input.
The small-generation and prime-actor source obligations give precisely the
global normalization premise of the existing exceptional assembly. The
two obligations, the earlier Cartan preparation, and local 5.1.13 remain
explicit. This is a conditional consumer, not a completed proof of 5.2.2.

Source: Aschbacher--Smith, 5.2.2 and its use in 12.2.2, pp.646--649,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

namespace ChosenModule
variable (D : ChosenModule T L V)
include D

/-- The original exceptional consumer, with its global-normalization
callback reduced to the two independent source branches of 5.2.2. -/
theorem rankOne_exceptional_cartan_of_prime_sources
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hescape : ¬ (normalizer (((T : Subgroup G).subgroupOf L) : Set L)).map L.subtype ≤
      normalizer (residual H : Set G))
    (hprepare : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n →
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      1 < ChapterE.generationParameter H → CartanPreparation T L H)
    (hlocal : SourceLocalCartanEscape KnownSimple.IsKnownSimple G)
    (hsmall : SourceCartanSmallGeneration KnownSimple.IsKnownSimple G)
    (hprime : SourceCartanPrimeExclusion KnownSimple.IsKnownSimple G) :
    CartanExceptionalConclusion T L (RankOneModule.wholeReduced T L) H ∧
      RankOneModule.ExceptionalExit T L H ∧ n = 2 ∧
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module := by
  apply D.rankOne_exceptional_cartan_of_source h hmany hn hpsl hH hgen hthree
    hescape hprepare hlocal
  intro h513 hs hHs hgs hts A B c hcontrol
  exact cartan_normalizes_of_prime_sources hsmall hprime h513 hs hHs hgs hts c hcontrol

end ChosenModule
end CFSG.Quasithin.Chapter12.Section02
