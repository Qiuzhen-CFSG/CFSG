module
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.SeededThreeCore
public import CFSG.Quasithin.ChapterD.Section02.JhatRestriction
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.Seed

/-!
# The original selected action's fully moved three-core factors

The local image's Sylow-fixed central seed and cyclic starred family give a
globally fixed supplement to the three-core support in the original Jhat.
The literal support action preserves the original minimum and starred actors,
and the finite D.2.16 decomposition is fully Fitting-moved. Thus this source
branch reaches its indecomposable factors without assuming full movement of
the original selected module.

Source: Aschbacher--Smith 15.1.2, printed p.1084, and D.2.25--29,
printed pp.190--192.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section01
open Theory.GroupTheory Stellmacher ChapterD ChapterD.UniqueFactor
open Section03 Section03.InitialSource ChapterA.Section05To06
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

theorem source_centralizing_seededThreeCore_factors
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    let H := Jhat ρ
    let σ := ρ.comp H.subtype
    (∀ A ∈ QhatStar ρ, rank A = 1) → cubicRatio ρ = 2 →
    (∀ A ∈ QhatStar σ, ⁅pCore 5 H,A⁆ = ⊥) →
    let U := subspaceCommutator σ ⊤ (pCore 3 H)
    ∃ d : RatioDecomposition.FactorData ρ H U,
      subspaceCommutator d.representation ⊤ (fittingSubgroup H) = ⊤ ∧
        ∃ c : RatioDecomposition.Decomposition d.representation, c.FittingFull := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  let H := Jhat ρ
  let := source_localAction_isSolvable hG T hempty hM
  let : H.Normal := Jhat_normal ρ
  dsimp only
  intro hrank hq hfive
  have hbound := source_centralizing_cubicRatio_le_two hG T hempty hM hmany hJ
  have hcore := cyclic_Jhat_core ρ (imageRepresentation_injective _ _ _)
    (source_localAction_twoCore hG T hM) hbound hrank
  obtain ⟨A,hA⟩ := (QhatStar_nonempty_iff ρ).mpr hbound
  have hqH : cubicRatio (ρ.comp H.subtype) = 2 :=
    (subgroup_starred_transport ρ H ⟨A,hA,le_sSup hA⟩).1.trans hq
  obtain ⟨hfix,hspan⟩ := source_localAction_seed_span hG T hM
  exact RatioDecomposition.seededThreeCore_factorData ρ
    (imageRepresentation_injective _ _ _) hbound H rfl hcore hqH hfive _ _ hfix hspan
end CFSG.Quasithin.Chapter15.Section01
