module
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.CyclicJoin
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.SelectedAction
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.Seed

/-!
# Selected-action cyclic normal-closure endpoint

The literal selected local action supplies the original SQTK cover, faithful
representation, Sylow-fixed generating seed, and two-core hypothesis. The
ambient cyclic rank-one branch therefore receives the normal-closure quotient
endpoint without changing the original actor or its source data.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterD ChapterD.UniqueFactor ChapterA.Section05To06 Stellmacher
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

theorem source_localAction_three_normalClosure
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    cubicRatio ρ = 2 → (∀ B ∈ QhatStar ρ, rank B = 1) →
    ∀ A : Subgroup D, A ∈ QhatStar ρ → ⁅pCore 5 D,A⁆ = ⊥ →
      normalClosure (A : Set D) ≤
        (pCore 2 (D ⧸ fittingSubgroup D)).comap (QuotientGroup.mk' (fittingSubgroup D)) := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  let f : M →* D := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
  let S := (T.subtype hM.1.2).mapSurjective (f := f)
    (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict_surjective
  let Z := AddSubgroup.toZModSubmodule 2 ((centralInvolutions T).subgroupOf V).toAddSubgroup
  let := source_localAction_isSolvable hG T hempty hM
  obtain ⟨hfix,hspan⟩ := source_localAction_seed_span hG T hM
  dsimp only
  intro hq hrank A hA hfive
  exact RatioDecomposition.source_three_normalClosure_le_twoCore_preimage ρ
    (imageRepresentation_injective _ _ _) (source_localAction_twoCore hG T hM)
    hq hrank
    (Chapter3.sqtk_of_mem_H hG (Chapter1.mem_H_of_isTwoLocal hM.1.1.1))
    f (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict_surjective
    S Z hfix hspan hA hfive

end CFSG.Quasithin.Chapter15.Section01
