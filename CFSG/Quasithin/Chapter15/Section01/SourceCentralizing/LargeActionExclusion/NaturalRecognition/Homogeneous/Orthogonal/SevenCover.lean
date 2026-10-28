module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalRecognition.Homogeneous.SeedSylow
public import Theory.Representation.BinaryPermutation.AlternatingEightSylowFixedExtension

/-!
# Exclusion of the seven-dimensional orthogonal cover in 15.1.28

A fixed lift modulo the literal moved module leaves a Sylow-fixed vector
in the seven-dimensional A8 core. Such vectors are constants and hence
component-fixed. This would make the original seed component-fixed,
contrary to its source movement. The argument includes an outer actor;
it never identifies the component with the full offender-generated group.

Source: Aschbacher--Smith 15.1.27(1)--28, printed pp.1102--1103.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterB.QuasisimpleSource
namespace OrthogonalExclusion
variable {D U : Type*} [Group D] [Finite D] [AddCommGroup U]
  [Module (ZMod 2) U] [Finite U]
/-- A moving Sylow-fixed seed rules out the seven-dimensional moved cover. -/
theorem not_seven_cover (σ : Representation (ZMod 2) D U) {K : Subgroup D}
    (s : MovedSection σ K) (P : Submodule (ZMod 2) U) (R : Sylow 2 K)
    (hfixed : P ≤ fixedSpace (σ.comp K.subtype) R)
    (hmoving : ¬ P ≤ Representation.invariants (σ.comp K.subtype)) :
    ¬ Nonempty (ActionEquiv (s.space.toRepresentation.comp K.subtype)
      (BinaryPermutation.alternatingCoreRepresentation (Fin 8))) := by
  rintro ⟨e⟩
  let N : Subrepresentation (σ.comp K.subtype) :=
    { toSubmodule := s.space.toSubmodule
      apply_mem_toSubmodule g v hv := s.space.apply_mem_toSubmodule g hv }
  apply hmoving
  apply hfixed.trans
  apply BinaryPermutation.fixedSpace_le_invariants_of_core_subrepresentation
    (σ.comp K.subtype) N ?_ e.groupEquiv e.linearEquiv e.intertwines R
  intro g v
  change σ (g : D) v - v ∈ s.space.toSubmodule
  rw [s.space_eq]
  exact Submodule.subset_span ⟨g,g.property,v,Submodule.mem_top,rfl⟩
end OrthogonalExclusion

open Stellmacher Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
open Theory.SpecificGroups.BinaryComponentResidual ChapterA.Section05To06 Section03 Section03.InitialSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource.SourceCompletion
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Literal recognized-component application, retaining both plane sizes. -/
theorem HasExchangedLinearSource.original_not_seven_cover
    {d : CaseIComponentData T M Mc V} (s : d.HasExchangedLinearSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (_hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (_hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (_hne : M ≠ Mc) (_hfull : V = localModule T M)
    (h : PreparedChosenModule T M V)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    let J := d.L ⊔ d.Q1
    let W := (d.U t).subgroupOf J
    let hr := d.exchanged_U_reduced_on_LQ1 s.1 hG hM hu h
      (s.c27Input hG h) s.cubicFacts t ht
    letI := hr.normal
    letI := hr.elementary
    let q := QuotientGroup.mk' (centralizer (W : Set J))
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    let B := offenderSubgroup ρ
    let K := ((d.L.subgroupOf J).map q).subgroupOf B
    ∀ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp B.subtype) K,
      ¬ Nonempty (ActionEquiv (c.sectionData.space.toRepresentation.comp K.subtype)
        (BinaryPermutation.alternatingCoreRepresentation (Fin 8))) := by
  intro J W hr
  let := hr.normal
  let := hr.elementary
  intro q ρ B K c
  obtain ⟨R,hfixed,hmoving⟩ := s.seed_component_sylow_fixed_and_moving hG hM hu h t ht htS c
  exact OrthogonalExclusion.not_seven_cover (ρ.comp B.subtype) c.sectionData
    (d.exchangedSeedSpace t J) R hfixed hmoving

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
