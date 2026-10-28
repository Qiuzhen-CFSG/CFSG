module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalRecognition.Homogeneous.SeedSylow

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalRecognition.Homogeneous.MovedSpace
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.FourBlock.FixedSupplement
/-!
# The original six-dimensional orthogonal branch is impossible

The literal commutator space has a fixed supplement. Its marked A₈ action
extends to S₈, including the outer case. Project the original moving
Sylow-fixed seed and carry Q₁'s actual offender into its stabilizer core;
the four-block model exclusion gives a contradiction.

Source: Aschbacher--Smith 15.1.27(1)--28, printed pp.1102--1103.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterB.QuasisimpleSource
open Stellmacher Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
open Theory.SpecificGroups.BinaryComponentResidual ChapterA.Section05To06 Section03 Section03.InitialSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource.SourceCompletion
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Literal recognized-component application, retaining both plane sizes. -/
theorem HasExchangedLinearSource.original_not_orthogonal_six
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
      ¬ IsAlternatingNatural (c.sectionData.space.toRepresentation.comp K.subtype) 8 := by
  intro J W hr
  let := hr.normal
  let := hr.elementary
  intro q ρ B K c
  obtain ⟨R,hfixed,hmoving⟩ := s.seed_component_sylow_fixed_and_moving hG hM hu h t ht htS c
  rintro ⟨e⟩
  let : K.Normal := c.fitting_eq.symm ▸ inferInstance
  have hsupp := (s.original_moved_space_and_supplement hG hM hu h t ht htS c).2
  obtain ⟨A,_hA,_hbest,hbest,hcore⟩ := s.original_seed_core_offender hG hM hu h t ht htS
  apply ChapterB.Offenders.Eight.FourBlock.no_natural_seed_core_offender
    (ρ.comp B.subtype) ((NormalElementaryQuotient.representation_injective W q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)).comp B.subtype_injective)
    c.sectionData.space K e.groupEquiv e.linearEquiv e.intertwines hsupp
    (d.exchangedSeedSpace t J) R hfixed hmoving (hbest.isOffender _) hcore

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
