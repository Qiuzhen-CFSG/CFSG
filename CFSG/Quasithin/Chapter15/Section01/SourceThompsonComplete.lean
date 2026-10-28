module
public import CFSG.Quasithin.Chapter15.Section01.SourceOmegaPrepared
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonAssembly
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonPrepared
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.PlaneSource
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# Complete preparation and Thompson conclusions in the centralizing branch

The full Omega core-containment proof finishes the chosen-module partition.
The proved Theorems A and C supply its universal source inputs. The numeric
plane branch becomes the original rank-two hypothesis, so the partition
retains only rank-two, natural orthogonal, and prepared chosen-module cases.

Every prepared chosen module supplies the local residual centralization of
15.1.12(4). It is independent of the choice of module and discharges the
remaining source premise of the Thompson-actor and generated-image theorem
15.1.13(3--4). The larger-case exclusions in 15.1.15 and the Section 15.2
argument remain separate.

Source: Aschbacher--Smith 15.1.11--13, printed pp.1089--1091, and the
rank-two entry 14.2.4, printed p.982.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open Chapter12.Section08 Chapter14.SourcePreliminaries
variable {G : Type*} [Group G] [Finite G]

/-- The centralizing source partition, with the full Omega preparation and
rank-two conversion proved on the original local module. -/
theorem source_prepared_chosen_or_rankTwo_complete
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    RankTwoHypothesis KnownSimple.IsKnownSimple T (sourceResidual M Mc) M ∨
    Nonempty (NaturalOrthogonalAction M V) ∨
    ∃ W : Subgroup G,
      (W = V ∨ ∃ U : Submodule (ZMod 2) (Additive V),
        SourceCases.Proper T M Mc V ρ U ∧
        W = (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype) ∧
      PreparedChosenModule T M W := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  rcases source_prepared_chosen_alternatives_from_AC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    hG T hempty hM hmany hJ hu hne with hsmall | hother
  · exact Or.inl (source_rankTwo_of_plane_numeric hG T hempty hM hmany hu hsmall.1 hsmall.2)
  · exact Or.inr hother

/-- Original 15.1.13(3--4), with the earlier local-residual centralization
and full Omega core containment discharged. -/
theorem source_lemma_15_1_13_3_4_centralizing_complete
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    RankTwoHypothesis KnownSimple.IsKnownSimple T (sourceResidual M Mc) M ∨
    Nonempty (NaturalOrthogonalAction M V) ∨
    ∃ W : Subgroup G,
      (W = V ∨ ∃ U : Submodule (ZMod 2) (Additive V),
        SourceCases.Proper T M Mc V ρ U ∧
        W = (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype) ∧
      W ≤ M ∧ W ≠ ⊥ ∧ ∃ hnW : M ≤ normalizer (W : Set G),
        ∃ hEW : IsElementaryAbelian 2 W,
          letI := hEW
          ChosenThompsonConclusions T M W hnW := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  rcases source_prepared_chosen_or_rankTwo_complete hG T hempty hM hmany hJ hu hne with
    hrank | hn | ⟨W, hW, hp⟩
  · exact Or.inl hrank
  · exact Or.inr (Or.inl hn)
  · have hres : ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
        omegaOneCenterAmbient (ChapterB.thompsonJ (T : Subgroup G) 1) ≤
          centralizer ((pResidual 2 H).map H.subtype : Set G) :=
      fun H hH => hp.thompson_omega_centralizes_residual hG T hempty hM hJ hH
    rcases source_lemma_15_1_13_3_4_centralizing hG T hempty hM hmany hJ hu hne hres with
      hsmall | hother
    · exact Or.inl (source_rankTwo_of_plane_numeric hG T hempty hM hmany hu hsmall.1 hsmall.2)
    · exact Or.inr hother

end CFSG.Quasithin.Chapter15.Section01
