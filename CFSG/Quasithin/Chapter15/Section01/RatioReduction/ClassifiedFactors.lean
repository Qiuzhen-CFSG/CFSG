module
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.ClassifiedFactors
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.NoncyclicSeed

/-!
# The classified starred partition of the selected local action

The original local subgroup M covers its faithful conjugation image on V(M).
Its proved solvability, trivial two-core, and cubic bound supply the complete
D.2 factor classification. Thus every factor's starred family is its Sylow
two-family, and the actual quotient action permutes the original blocks,
actors, and support spaces. The noncyclic source application constructs both
the full Fitting-moved decomposition and this ambient permutation directly
from a single original noncyclic starred actor.

Source: Aschbacher--Smith 15.1.2, first paragraph, printed p.1084.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterD ChapterD.RatioDecomposition ChapterD.UniqueFactor
open ChapterA.Section05To06 Stellmacher
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- Every factor obtained from the original local action has exactly the
original Sylow starred family, with the actual quotient map from M. -/
theorem source_localAction_factor_starred_sylow
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    ∀ (U : Submodule (ZMod 2) (Additive (localModule T M)))
      (c : FactorData ρ (Jhat ρ) U) (d : Decomposition c.representation), d.FittingFull →
    ∀ i (A : Subgroup (d.factor i).Carrier), A ∈ QhatStar (d.factor i).action ↔
      ∃ S : Sylow 2 (d.factor i).Carrier, (S : Subgroup _) = A := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  let f := actionHom M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  let := source_localAction_isSolvable hG T hempty hM
  let : (Jhat ρ).Normal := Jhat_normal ρ
  dsimp only
  intro U c d hd
  exact c.factor_starred_sylow_iff d (source_localAction_twoCore hG T hM)
    (source_centralizing_cubicRatio_le_two hG T hempty hM hmany hJ) hd
    (Chapter3.sqtk_of_mem_H hG (Chapter1.mem_H_of_isTwoLocal hM.1.1.1))
    f.rangeRestrict f.rangeRestrict_surjective

/-- The literal source factor family carries the original quotient action
on its starred blocks, embedded actors and commutator supports. -/
theorem source_localAction_classified_partition
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let D := internalActionImage M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    ∀ (U : Submodule (ZMod 2) (Additive (localModule T M)))
      (c : FactorData ρ (Jhat ρ) U) (d : Decomposition c.representation), d.FittingFull →
    ∃ π : D →* Equiv.Perm d.Index,
      (⋃ i, c.ambientBlock d i) = QhatStar ρ ∧ Jhat ρ ≤ π.ker ∧ ∀ g i,
      Subgroup.map (MulAut.conj g).toMonoidHom '' c.ambientBlock d i = c.ambientBlock d (π g i) ∧
      (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g i)).actor ∧
      (c.ambientFactor d i).space.map (ρ g) = (c.ambientFactor d (π g i)).space := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  dsimp only
  intro U c d hd
  exact c.source_Jhat_partition_action rfl d
    (source_localAction_factor_starred_sylow hG T hempty hM hmany hJ U c d hd)

/-- In the original noncyclic source branch both the factor family and its
ambient classified permutation are constructed from the selected local data. -/
theorem source_centralizing_noncyclic_classified_partition
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let D := internalActionImage M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    let K := Jhat ρ
    let U := subspaceCommutator ρ ⊤ (K ⊓ fittingSubgroup D)
    ∀ A : Subgroup D, A ∈ QhatStar ρ → 1 < rank A →
    ∃ (c : FactorData ρ K U) (d : Decomposition c.representation), d.FittingFull ∧
      ∃ π : D →* Equiv.Perm d.Index,
        (⋃ i, c.ambientBlock d i) = QhatStar ρ ∧ K ≤ π.ker ∧ ∀ g i,
        Subgroup.map (MulAut.conj g).toMonoidHom '' c.ambientBlock d i = c.ambientBlock d (π g i) ∧
        (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
          (c.ambientFactor d (π g i)).actor ∧
        (c.ambientFactor d i).space.map (ρ g) = (c.ambientFactor d (π g i)).space := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  dsimp only
  intro A hA hr
  obtain ⟨c,_,d,hd⟩ := source_centralizing_noncyclic_seed_factors hG T hempty hM hmany hJ A hA hr
  exact ⟨c,d,hd,source_localAction_classified_partition hG T hempty hM hmany hJ _ c d hd⟩
end CFSG.Quasithin.Chapter15.Section01
