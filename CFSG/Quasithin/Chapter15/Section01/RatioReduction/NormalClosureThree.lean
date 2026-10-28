module
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.NormalClosureThree
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.SeededThreeCore
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.NoncyclicSeed

/-!
# An original non-quintic actor with the actual selected seed

At cubic ratio two, the original Sylow-fixed seed excludes noncyclic
starred actors. The normal closure of a specified actor centralizing the
five-core therefore admits the literal three-core reduction, even when
other ambient actors move the five-core. This applies the unchanged
representation, normal closure, and central seed of the selected subgroup.

Source: Aschbacher--Smith 15.1.2, first paragraph, printed p.1084.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterD ChapterD.RatioDecomposition ChapterD.UniqueFactor
open ChapterA.Section05To06 Stellmacher
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- An individual non-quintic original actor has its own three-core factor family,
using the selected Sylow seed even when other original stars move O5. -/
theorem source_localAction_three_normalClosure_factors
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M)
 :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    ∀ A : Subgroup D, A ∈ QhatStar ρ → cubicRatio ρ = 2 →
      ⁅pCore 5 D,A⁆ = ⊥ →
      let N := normalClosure (A : Set D)
      let P := (pCore 3 N).map N.subtype
      ∃ d : FactorData ρ N (subspaceCommutator ρ ⊤ P),
        subspaceCommutator d.representation ⊤ (fittingSubgroup N) = ⊤ ∧
          ∃ c : Decomposition d.representation, c.FittingFull := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  let := source_localAction_isSolvable hG T hempty hM
  let f : M →* D := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
  let S := (T.subtype hM.1.2).mapSurjective (f := f)
    (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict_surjective
  let Z := AddSubgroup.toZModSubmodule 2 ((centralInvolutions T).subgroupOf V).toAddSubgroup
  obtain ⟨hfix,hspan⟩ := source_localAction_seed_span hG T hM
  dsimp only
  intro A hA hq hfive
  refine source_three_normalClosure_seed_factors ρ
    (imageRepresentation_injective _ _ _) (source_localAction_twoCore hG T hM)
    hq (fun B hB => ?_) hA hfive S Z hfix hspan
  · have hc : IsCyclic B := by
      have h := source_localAction_noncyclic_seed_ratio hG T hempty hM
      by_contra hn
      have hrB : 1 < rank B := by
        have hp := hB.1.2.1.rank_pos
        by_contra hm
        have he : rank B = 1 := by omega
        have hcard : Nat.card B = 2 := by rw [hB.1.2.1.card_eq_two_pow_rank,he]; norm_num
        exact hn (isCyclic_of_prime_card hcard)
      have hh := (h B hB hrB).1
      rw [hq] at hh
      have hreal := congrArg ENNReal.toReal hh
      norm_num at hreal
    let := hc
    exact CyclicSource.rank_one_of_cyclic ρ hB hc
end CFSG.Quasithin.Chapter15.Section01
