module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.Noncyclic
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.Seed
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.BeforeMoved.Seed
/-!
# The selected noncyclic actor branch with its original seed

The literal selected action on V(M) carries the actual SQTK cover and the
Sylow-fixed generating seed. A single original noncyclic starred actor
therefore forces ratio 3/2, excluding all original rank-one starred actors.
This supplies the all-noncyclic premise of the existing odd-kernel and
finite factor-decomposition consumer without asserting it from existence
alone.

Source: Aschbacher--Smith 15.1.2, printed p.1084, and D.2.19, pp.187--188.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterD ChapterD.UniqueFactor ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The actual Sylow-fixed generating seed excludes mixed starred families
as soon as one original starred actor is noncyclic. -/
theorem source_localAction_noncyclic_seed_ratio
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let D := internalActionImage M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    ∀ A : Subgroup D, A ∈ QhatStar ρ → 1 < rank A →
      cubicRatio ρ = 3 / 2 ∧ ∀ B ∈ QhatStar ρ, 1 < rank B := by
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
  intro A hA hr
  exact BeforeMoved.source_noncyclic_seed_ratio ρ
    (Chapter3.sqtk_of_mem_H hG (Chapter1.mem_H_of_isTwoLocal hM.1.1.1)) f
    (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict_surjective
    (imageRepresentation_injective _ _ _) (source_localAction_twoCore hG T hM)
    S Z hfix hspan hA hr

/-- A single original noncyclic starred actor suffices for the actual
fully Fitting-moved reduction and finite indecomposable decomposition. -/
theorem source_centralizing_noncyclic_seed_factors
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    let K := Jhat ρ
    let P := K ⊓ fittingSubgroup D
    ∀ A : Subgroup D, A ∈ QhatStar ρ → 1 < rank A →
      ∃ d : RatioDecomposition.FactorData ρ K (subspaceCommutator ρ ⊤ P),
        subspaceCommutator d.representation ⊤ (fittingSubgroup K) = ⊤ ∧
        ∃ c : RatioDecomposition.Decomposition d.representation, c.FittingFull := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  dsimp only
  intro A hA hr
  exact source_centralizing_noncyclic_factors hG T hempty hM hmany hJ
    (source_localAction_noncyclic_seed_ratio hG T hempty hM A hA hr).2
end CFSG.Quasithin.Chapter15.Section01
