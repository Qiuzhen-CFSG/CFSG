module
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.NoSmallThree
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.SelectedAction

/-!
# The selected local action in the no-small-three cyclic case

The original centralizing row supplies the faithful conjugation image,
solvability, trivial two-core and cubic bound. When its original starred
actors are cyclic and its three-core has no two-dimensional cubic support,
the proved fixed supplement constructs the literal fully Fitting-moved
Jhat action and finite D.2 factor family. The displayed ratio-two and
five-core alternatives are the genuine case assumptions.

Source: Aschbacher--Smith 15.1.2, first paragraph, printed p.1084.
-/

public section
open Subgroup Representation Representation.BinaryOffender

namespace CFSG.Quasithin.Chapter15.Section01
open Theory.GroupTheory Stellmacher ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition
open Section03 Section03.InitialSource ChapterA.Section05To06
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- The no-small-three cyclic branch of original 15.1.2 constructs its actual
indecomposable factor family without a prior odd-kernel factorization. -/
theorem source_centralizing_noSmallThree_factors
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
    (∀ X : Subgroup H, X ≤ pCore 3 H → Nat.card X = 3 →
      Module.finrank (ZMod 2) (subspaceCommutator σ ⊤ X) ≠ 2) →
    ∃ d : FactorData ρ H (subspaceCommutator σ ⊤ (pCore 3 H)),
      subspaceCommutator d.representation ⊤ (fittingSubgroup H) = ⊤ ∧
        ∃ c : Decomposition d.representation, c.FittingFull := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  let H := Jhat ρ
  let := source_localAction_isSolvable hG T hempty hM
  dsimp only
  intro hrank hq hfive hNo
  have hbound := source_centralizing_cubicRatio_le_two hG T hempty hM hmany hJ
  have hcore := cyclic_Jhat_core ρ (imageRepresentation_injective _ _ _)
    (source_localAction_twoCore hG T hM) hbound hrank
  obtain ⟨A,hA⟩ := (QhatStar_nonempty_iff ρ).mpr hbound
  have hqH : cubicRatio (ρ.comp H.subtype) = 2 :=
    (subgroup_starred_transport ρ H ⟨A,hA,le_sSup hA⟩).1.trans hq
  exact noSmallThree_factorData ρ (imageRepresentation_injective _ _ _) hbound
    H rfl hcore hqH hfive hNo
end CFSG.Quasithin.Chapter15.Section01
