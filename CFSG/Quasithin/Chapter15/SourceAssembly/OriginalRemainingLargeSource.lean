module

public import CFSG.Quasithin.Chapter15.SourceAssembly.OriginalLargeSource
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineNormalization
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableThreeExclusion

/-!
# Theorem E after the original Nine and cubic decomposable source proofs

Full-module normalization remains only for the extraspecial action and the
prime-five decomposable action. The original marked Thompson pair is constructed
from the same decomposable witness; its prime-three alternative is excluded by
the proved cubic source contradiction. The full Nine action has its original
centralizer normalization independently proved.

The rank-two resolver, these two normalization duties, the subsequent large
action exclusion, and original 15.3.13 remain inputs to this assembly.
Source: Aschbacher--Smith 15.1.3, 15.1.14--15 and 15.3.13.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The two remaining normalization cases, retaining the actual prime-five
Thompson pair and all original decomposable factor data. -/
@[expose] def OriginalRemainingLargeAction (T : Sylow 2 G) (M V : Subgroup G)
    (h : PreparedChosenModule T M V) : Prop :=
  letI := h.elementary
  let ρ := imageRepresentation M V h.normalized
  let f := (actionHom M V h.normalized).rangeRestrict
  let S := ((T : Subgroup G).subgroupOf M).map f
  SourceCases.Extraspecial ρ S ∨
    (cubicRatio ρ = 2 ∧
      ∃ (U : Submodule (ZMod 2) (Additive V)) (c : FactorData ρ (Jhat ρ) U)
        (d : Decomposition c.representation)
        (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
        (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
        d.FittingFull ∧
        (∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
          (c.ambientFactor d (π g i)).actor) ∧
        (∀ g i, (c.ambientFactor d i).space.map (ρ g) =
          (c.ambientFactor d (π g i)).space) ∧
        SourceCases.Decomposable ρ (T : Subgroup G) M f c d π ∧ s.prime = 5)

/-- Original full normalization restricted to extraspecial and prime-five
decomposable actions at the actual singleton centralizer. -/
abbrev OriginalRemainingFullNormalizationAt (T : Sylow 2 G) (Mc : Subgroup G) : Prop :=
  ¬ ClassificationModels.IsTheoremEModel G →
    (∀ N : Subgroup G, IsOrderingMaximal T N →
      ¬ Nonempty (NaturalOrthogonalAction N (localModule T N))) →
    ∀ (M : Subgroup G) (_hM : IsOrderingMaximal T M), M ≠ Mc →
      elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G) →
      ∀ hp : PreparedChosenModule T M (localModule T M),
        letI := hp.elementary
        let V := localModule T M
        let D := internalActionImage M V hp.normalized
        let S := ((T : Subgroup G).subgroupOf M).map
          (actionHom M V hp.normalized).rangeRestrict
        4 ∣ Nat.card D →
        ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
          (actionHom M V hp.normalized).rangeRestrict < S →
        OriginalRemainingLargeAction T M V hp →
        centralizer (centralInvolutions T : Set G) ≤
          normalizer (thompsonFixed T V : Set G)

/-- The completed Nine and prime-three source proofs supply those branches of
the original full normalization duty. -/
theorem original_large_full_normalization_of_remaining
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hnormalize : OriginalRemainingFullNormalizationAt T Mc) :
    OriginalLargeFullNormalizationAt T Mc := by
  intro hnot hn M hM hne hJ h
  let := h.elementary
  dsimp only
  intro hfour hstrict hlarge
  rcases hlarge with h9 | hextra | ⟨hq,U,c,d,π,hd,hp,hs,hdec⟩
  · exact h.nine_full_centralizer_normalizes_thompsonFixed
      hG T hempty hM hmany hJ hu hne rfl h9
  · exact hnormalize hnot hn M hM hne hJ h hfour hstrict (Or.inl hextra)
  · obtain ⟨s⟩ := DecomposableMarker.thompsonPair_of_decomposable
      hG T hempty hM hmany hJ h rfl c d hd π hp hs hdec hq
    rcases s.prime_cases with hthree | hfive
    · exact (h.false_of_decomposable_three_source
        hG T hempty hM hmany hJ hu hne rfl c d hd s π hp hs hdec hq hthree).elim
    · exact hnormalize hnot hn M hM hne hJ h hfour hstrict
        (Or.inr ⟨hq,U,c,d,s,π,hd,hp,hs,hdec,hfive⟩)

/-- Theorem E with the Nine and prime-three normalization branches supplied
by their original source proofs. All remaining duties retain their original
ambient group, Sylow subgroup and singleton centralizer. -/
theorem source_theoremE_of_original_remaining_sources
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
      SourceLargeChosenExclusionInput hG T Mc)
    (h13 : ∀ d : CharacteristicTwo.LocalData G, d.T = T →
      IsOrderingMaximal d.T d.M →
      maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc} →
      ∀ Yplus : Subgroup G, Hypothesis15310 d.M d.Y d.S d.V₁ Yplus →
      primeRank 3 Yplus = 2 →
      ∀ I ∈ outsideFamily Yplus d.S d.M, generalizedFitting I ≠ pCore 2 I) :
    ClassificationModels.IsTheoremEModel G := by
  exact source_theoremE_of_original_large_sources hG T hmany hempty hrank
    (fun Mc hu => original_large_full_normalization_of_remaining
      hG T hmany hempty hu (hnormalize Mc hu)) hlarge h13

end CFSG.Quasithin.Chapter15
