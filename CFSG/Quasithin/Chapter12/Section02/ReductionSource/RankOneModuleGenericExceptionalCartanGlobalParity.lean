module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalSmallGenerationParity
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanGlobal

/-!
# Applying the Cartan parity theorem to the original chosen module

The parity clause of original 5.1.6 removes the odd-exponent branch of the
local-to-global normalization argument. It also removes the parity premise
from the existing small-Cartan source assembly. The latter application keeps
the higher-degree and prime-actor source arguments explicit; it is not a
completed proof of 5.2.2. This task retains their discharge.

Source: Aschbacher--Smith, 5.1.6 and 5.2.2, printed pp.632,646--649,
and their use in 12.2.2, printed p.795 (`refs/quasithin.pdf`).
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

/-- The original chosen-module consumer in odd degree, using the proved
normalization implication and the earlier local escape theorem. -/
theorem rankOne_exceptional_cartan_of_odd
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
    (hodd : Odd n) :
    CartanExceptionalConclusion T L (RankOneModule.wholeReduced T L) H ∧
      RankOneModule.ExceptionalExit T L H ∧ n = 2 ∧
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module := by
  apply D.rankOne_exceptional_cartan_of_source h hmany hn hpsl hH hgen hthree
    hescape hprepare hlocal
  intro _h513 hs hHs _hgs _hts A B c hcontrol
  exact hs.cartan_normalizes_of_odd hHs c hcontrol hodd

/-- The same literal chosen-module consumer with the small-generation
premise reduced to the higher-degree source branch. -/
theorem rankOne_exceptional_cartan_of_higher_and_prime
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
    (hhigher : SourceCartanHigherFieldReduction KnownSimple.IsKnownSimple G)
    (hprime : SourceCartanPrimeExclusion KnownSimple.IsKnownSimple G) :
    CartanExceptionalConclusion T L (RankOneModule.wholeReduced T L) H ∧
      RankOneModule.ExceptionalExit T L H ∧ n = 2 ∧
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module := by
  exact D.rankOne_exceptional_cartan_of_prime_sources h hmany hn hpsl hH hgen hthree
    hescape hprepare hlocal (sourceCartanSmallGeneration_of_higher_knownSimple hhigher) hprime

end ChosenModule
end CFSG.Quasithin.Chapter12.Section02
