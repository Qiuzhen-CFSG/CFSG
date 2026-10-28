module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalRecognition.Homogeneous.Exterior.SourceCoordinates
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Exterior.SourceFF.Offenders
public import Theory.Representation.SL5ExteriorSquare.SeedCoreGeometry

/-!
# Exclusion of the degree-ten exterior branch in original 15.1.28

A nonzero Sylow-fixed exterior seed has a conjugate 2+3 parabolic stabilizer.
Its two-core lies in the hyperplane parabolic, where the best-offender
classification forces every best offender to equal the whole shear radical.
That radical is not contained in the seed stabilizer's two-core.

The literal source consumer supplies the split coordinates and original Q1
best offender, so the degree-ten branch is excluded without a remaining
model or coordinate premise. The existing graph-twisted coordinates include
the exterior cube. Final natural-module assembly remains with the
natural-recognition family.

Source: Aschbacher--Smith 15.1.27(2)--28, printed pp.1102--1103.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section01
namespace ExteriorReduction
open Representation.SL5TenDimensional Representation.SL5ExteriorSquare

/-- No best offender lies in the two-core of a nonzero Sylow-fixed seed. -/
theorem modelSeedCoreExclusion : ModelSeedCoreExclusion := by
  intro R P hn hf A hA hcore
  obtain ⟨g,hg⟩ := seedKernel_conjugate_parabolic_two R P hn hf
  let f : Group →* Group := (MulAut.conj g).toMonoidHom
  have hfinj : Function.Injective f := (MulAut.conj g).injective
  have hm := Subgroup.map_mono (f := f) hcore
  rw [map_pCoreIn_of_injective 2 (subspaceKernel (exteriorAction 2) P ⊤) f hfinj,
    hg] at hm
  have he := ChapterK.Linear.Exterior.SourceFF.best_le_parabolic_eq_shear
    (hA.map_conj (exteriorAction 2) g) (hm.trans twoCore_parabolic_two_le_four)
  rw [he] at hm
  exact shear_not_le_twoCore_parabolic_two hm

end ExteriorReduction
open Stellmacher Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
open Theory.SpecificGroups.BinaryComponentResidual ChapterA.Section05To06 Section03 Section03.InitialSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.SourceCompletion
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The original exterior alternative is impossible, for both source plane sizes
and both graph-related exterior powers, on the literal recognized component. -/
theorem HasExchangedLinearSource.original_exterior_false
    {d : CaseIComponentData T M Mc V} (s : d.HasExchangedLinearSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hfull : V = localModule T M)
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
      BinaryActor.ActionCase (ρ.comp B.subtype) K c.sectionData 5 →
      IsIrreducible (c.sectionData.space.toRepresentation.comp K.subtype) →
      Module.finrank (ZMod 2) c.sectionData.space.toSubmodule = 10 →
      (K ≃* Representation.SL5TenDimensional.Group) →
      False := by
  intro J W hr
  let := hr.normal
  let := hr.elementary
  intro q ρ B K c hc hirr hdim mark
  exact s.original_exterior_false_of_model_core hG hempty hM hmany hJ hu
    hne hfull h t ht htS c hc hirr hdim mark ExteriorReduction.modelSeedCoreExclusion

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
