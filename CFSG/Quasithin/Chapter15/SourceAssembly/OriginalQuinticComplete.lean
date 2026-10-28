module

public import CFSG.Quasithin.Chapter15.SourceAssembly.OriginalNormalizedPrimeSource
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableQuinticSource.Exclusion

/-!
# The original quintic exclusion supplied to Theorem E

The actual point-centralizer contradiction proves the remaining order-five
callback. The frozen order-fifteen exclusion then supplies the complete
original quintic duty. Theorem E retains only its independent rank-two and
15.3.13 callbacks, with every original Sylow guard unchanged.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15
open Section01 Section03 ChapterA.Section05To06
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The remaining original quintic prime callback is proved by the literal
point-component contradiction with its original quotient denominator. -/
theorem original_quintic_prime_exclusion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc}) :
    OriginalQuinticPrimeExclusionAt T Mc := by
  intro _hnot _hn M hM hne hJ h
  let := h.elementary
  intro _hres _hbounds U c d hd s π hp hs hdec hq hfive
  exact h.decomposable_five_prime_residual_false hG T hempty hM hmany hJ hu hne rfl
    c d hd s π hp hs hdec hq hfive

/-- Both actual residual orders now supply the original broad quintic exclusion. -/
theorem original_quintic_exclusion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc}) :
    OriginalQuinticExclusionAt T Mc :=
  original_quintic_exclusion_of_prime_residual hG T hmany hempty hu
    (original_quintic_prime_exclusion hG T hmany hempty hu)

/-- Theorem E with the complete original quintic callback supplied internally. -/
theorem source_theoremE_of_original_quintic_complete
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hrank : ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
      RankTwoResolver T Mc)
    (h13 : ∀ d : CharacteristicTwo.LocalData G, d.T = T →
      IsOrderingMaximal d.T d.M →
      maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc} →
      ∀ Yplus : Subgroup G, Hypothesis15310 d.M d.Y d.S d.V₁ Yplus →
      primeRank 3 Yplus = 2 →
      ∀ I ∈ outsideFamily Yplus d.S d.M, generalizedFitting I ≠ pCore 2 I) :
    ClassificationModels.IsTheoremEModel G := by
  exact source_theoremE_of_original_normalized_prime_sources hG T hmany hempty hrank
    (fun _ hu => original_quintic_prime_exclusion hG T hmany hempty hu) h13

end CFSG.Quasithin.Chapter15
