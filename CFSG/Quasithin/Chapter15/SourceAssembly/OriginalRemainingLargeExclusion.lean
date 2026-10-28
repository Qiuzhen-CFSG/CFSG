module

public import CFSG.Quasithin.Chapter15.SourceAssembly.OriginalRemainingLargeSource
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceLargeChosenNineExclusion

/-!
# Original Theorem E with only the two remaining large-action cases

The full original Nine action is impossible: its cyclic Sylow action makes the
Thompson image proper, whereas the cubic source proof makes the two images
equal. Together with the prime-three decomposable contradiction, this restricts
the subsequent 15.1.15 exclusion to the same extraspecial and prime-five cases
that remain for normalization.

This assembly still requires those source duties, the original rank-two
resolver and original 15.3.13.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The subsequent source exclusion, restricted to the two surviving large
actions while retaining the original 15.1.14 premises. -/
abbrev OriginalRemainingLargeExclusionAt (T : Sylow 2 G) (Mc : Subgroup G) : Prop :=
  ¬ ClassificationModels.IsTheoremEModel G →
  (∀ N : Subgroup G, IsOrderingMaximal T N →
    ¬ Nonempty (NaturalOrthogonalAction N (localModule T N))) →
  ∀ (M : Subgroup G) (_hM : IsOrderingMaximal T M), M ≠ Mc →
    elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G) →
    ∀ hp : PreparedChosenModule T M (localModule T M),
      (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
        (centralizer (centralInvolutions T : Set G)).subtype ≤
          centralizer (thompsonFixed T (localModule T M) : Set G) →
      (M ⊓ normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤
          normalizer (thompsonFixed T (localModule T M) : Set G) ∧
        normalizer (thompsonFixed T (localModule T M) : Set G) ≤ Mc ∧
        normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤ M ⊓ Mc) →
      ¬ OriginalRemainingLargeAction T M (localModule T M) hp

/-- Original Nine and cubic decomposable sources are impossible, so later
large-action exclusion needs only the two remaining cases. -/
theorem original_large_exclusion_of_remaining
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hlarge : OriginalRemainingLargeExclusionAt T Mc) :
    SourceLargeChosenExclusionInput hG T Mc := by
  intro hnot hn M hM hne hJ h hres hbounds haction
  let := h.elementary
  rcases haction with h9 | hextra | ⟨hq,U,c,d,π,hd,hp,hs,hdec⟩
  · exact h.false_of_full_nine hG T hempty hM hmany hJ hu hne rfl h9
  · exact hlarge hnot hn M hM hne hJ h hres hbounds (Or.inl hextra)
  · obtain ⟨s⟩ := DecomposableMarker.thompsonPair_of_decomposable
      hG T hempty hM hmany hJ h rfl c d hd π hp hs hdec hq
    rcases s.prime_cases with hthree | hfive
    · exact h.false_of_decomposable_three_source
        hG T hempty hM hmany hJ hu hne rfl c d hd s π hp hs hdec hq hthree
    · exact hlarge hnot hn M hM hne hJ h hres hbounds
        (Or.inr ⟨hq,U,c,d,s,π,hd,hp,hs,hdec,hfive⟩)

/-- The original Theorem E assembly after both Nine duties and the
prime-three decomposable source have been discharged. -/
theorem source_theoremE_of_original_two_large_sources
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hrank : ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
      RankTwoResolver T Mc)
    (hnormalize : ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
      OriginalRemainingFullNormalizationAt T Mc)
    (hlarge : ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
      OriginalRemainingLargeExclusionAt T Mc)
    (h13 : ∀ d : CharacteristicTwo.LocalData G, d.T = T →
      IsOrderingMaximal d.T d.M →
      maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc} →
      ∀ Yplus : Subgroup G, Hypothesis15310 d.M d.Y d.S d.V₁ Yplus →
      primeRank 3 Yplus = 2 →
      ∀ I ∈ outsideFamily Yplus d.S d.M, generalizedFitting I ≠ pCore 2 I) :
    ClassificationModels.IsTheoremEModel G := by
  exact source_theoremE_of_original_remaining_sources hG T hmany hempty hrank hnormalize
    (fun Mc hu => original_large_exclusion_of_remaining
      hG T hmany hempty hu (hlarge Mc hu)) h13

end CFSG.Quasithin.Chapter15
