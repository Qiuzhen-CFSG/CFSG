module

public import CFSG.Quasithin.Chapter15.SourceAssembly.OriginalRemainingLargeExclusion
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceLargeChosenExtraspecialExclusion

/-!
# Theorem E after the original extraspecial catalogue exclusion

The actual selected-component catalogue proves the extraspecial contradiction
from the preceding residual conclusion. Subsequent large-action exclusion
therefore remains only for the prime-five decomposable action, with its same
factor data, supports and Thompson pair. Normalization for extraspecial and
prime-five actions, the rank-two resolver and original 15.3.13 remain inputs.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The remaining later exclusion, on the literal prime-five decomposable
source with the preceding residual and normalizer conclusions. -/
abbrev OriginalQuinticExclusionAt (T : Sylow 2 G) (Mc : Subgroup G) : Prop :=
  ¬ ClassificationModels.IsTheoremEModel G →
  (∀ N : Subgroup G, IsOrderingMaximal T N →
    ¬ Nonempty (NaturalOrthogonalAction N (localModule T N))) →
  ∀ (M : Subgroup G) (_hM : IsOrderingMaximal T M), M ≠ Mc →
    elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G) →
    ∀ h : PreparedChosenModule T M (localModule T M),
      letI := h.elementary
      (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
        (centralizer (centralInvolutions T : Set G)).subtype ≤
          centralizer (thompsonFixed T (localModule T M) : Set G) →
      (M ⊓ normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤
          normalizer (thompsonFixed T (localModule T M) : Set G) ∧
        normalizer (thompsonFixed T (localModule T M) : Set G) ≤ Mc ∧
        normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤ M ⊓ Mc) →
      ∀ {U : Submodule (ZMod 2) (Additive (localModule T M))}
        (c : FactorData (imageRepresentation M (localModule T M) h.normalized)
          (Jhat (imageRepresentation M (localModule T M) h.normalized)) U)
        (d : Decomposition c.representation), d.FittingFull →
      ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
        (π : internalActionImage M (localModule T M) h.normalized →* Equiv.Perm d.Index),
        (∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
          (c.ambientFactor d (π g i)).actor) →
        (∀ g i, (c.ambientFactor d i).space.map
            (imageRepresentation M (localModule T M) h.normalized g) =
          (c.ambientFactor d (π g i)).space) →
        SourceCases.Decomposable (imageRepresentation M (localModule T M) h.normalized)
          (T : Subgroup G) M (actionHom M (localModule T M) h.normalized).rangeRestrict
          c d π →
        cubicRatio (imageRepresentation M (localModule T M) h.normalized) = 2 →
        s.prime = 5 → False

/-- The completed extraspecial catalogue argument supplies that row of the
later exclusion; only the literal quintic row remains. -/
theorem original_remaining_exclusion_of_quintic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hquintic : OriginalQuinticExclusionAt T Mc) :
    OriginalRemainingLargeExclusionAt T Mc := by
  intro hnot hn M hM hne hJ h hres hbounds haction
  let := h.elementary
  rcases haction with hextra | ⟨hq,U,c,d,s,π,hd,hp,hs,hdec,hfive⟩
  · exact h.false_of_full_extraspecial_after_residual
      hG T hempty hM hmany hJ hu hne rfl hextra hres
  · exact hquintic hnot hn M hM hne hJ h hres hbounds c d hd s π hp hs hdec hq hfive

/-- Theorem E with the original Nine, cubic decomposable and later
extraspecial exclusions supplied internally. -/
theorem source_theoremE_of_original_quintic_source
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
    (hquintic : ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
      OriginalQuinticExclusionAt T Mc)
    (h13 : ∀ d : CharacteristicTwo.LocalData G, d.T = T →
      IsOrderingMaximal d.T d.M →
      maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc} →
      ∀ Yplus : Subgroup G, Hypothesis15310 d.M d.Y d.S d.V₁ Yplus →
      primeRank 3 Yplus = 2 →
      ∀ I ∈ outsideFamily Yplus d.S d.M, generalizedFitting I ≠ pCore 2 I) :
    ClassificationModels.IsTheoremEModel G := by
  exact source_theoremE_of_original_two_large_sources hG T hmany hempty hrank hnormalize
    (fun Mc hu => original_remaining_exclusion_of_quintic
      hG T hmany hempty hu (hquintic Mc hu)) h13

end CFSG.Quasithin.Chapter15
