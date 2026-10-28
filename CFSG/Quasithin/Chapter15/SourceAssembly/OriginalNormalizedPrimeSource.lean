module

public import CFSG.Quasithin.Chapter15.SourceAssembly.OriginalFullNormalization
public import CFSG.Quasithin.Chapter15.SourceAssembly.OriginalQuinticPrimeExclusionSource

/-!
# Theorem E with original full normalization proved

The extraspecial, nine, and decomposable source proofs supply the entire
normalization duty at the original singleton centralizer. The remaining
inputs are the rank-two resolver, the later prime-residual quintic exclusion,
and original 15.3.13, with their original groups and Sylow guards retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15
open Section01 Section03 ChapterA.Section05To06
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original full normalization result removes that hypothesis from
Theorem E, while retaining the independent original exclusion duties. -/
theorem source_theoremE_of_original_normalized_prime_sources
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hrank : ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
      RankTwoResolver T Mc)
    (hquintic : ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
      OriginalQuinticPrimeExclusionAt T Mc)
    (h13 : ∀ d : CharacteristicTwo.LocalData G, d.T = T →
      IsOrderingMaximal d.T d.M →
      maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc} →
      ∀ Yplus : Subgroup G, Hypothesis15310 d.M d.Y d.S d.V₁ Yplus →
      primeRank 3 Yplus = 2 →
      ∀ I ∈ outsideFamily Yplus d.S d.M, generalizedFitting I ≠ pCore 2 I) :
    ClassificationModels.IsTheoremEModel G := by
  exact source_theoremE_of_original_quintic_source hG T hmany hempty hrank
    (fun Mc hu => original_remaining_full_normalization hG T hmany hempty hu)
    (fun Mc hu => original_quintic_exclusion_of_prime_residual
      hG T hmany hempty hu (hquintic Mc hu)) h13

end CFSG.Quasithin.Chapter15
