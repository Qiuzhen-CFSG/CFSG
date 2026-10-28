module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.Source
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.SourceAssembly
/-!
# The literal selected action supplied to D.2

The original M acts faithfully on V(M) through its conjugation image.
Reducedness gives a trivial two-core, and the empty faithful-component
hypothesis makes that image solvable. The proved cubic bound therefore
supplies an actual minimum actor, which moves an odd prime core at three
or five. The noncyclic consumer retains the literal quotient map from M,
discharges its SQTK cover and all action hypotheses, and applies D.2.19.
Its full Fitting-moved input belongs to the subsequent source splitting.
Source: Aschbacher--Smith 15.1.2, first paragraph, p.1084; D.2.13--19,
pp.184--188.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterD ChapterD.UniqueFactor ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem source_localAction_isSolvable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M) :
    Group.IsSolvable (internalActionImage M (localModule T M) (le_normalizer_conjugateSpanBy _ _)) := by
  let f := actionHom M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  have hr := residual_le_centralizer_localModule
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    hG T hempty ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  have hk : solvableResidual M ≤ f.ker := by
    rw [show f.ker = (centralizer (_ : Set G)).subgroupOf M from actionHom_ker M _ _]
    exact fun _ hx => hr (mem_map_of_mem _ hx)
  have hz : solvableResidual f.range = ⊥ := by
    rw [←map_solvableResidual_eq f.rangeRestrict f.rangeRestrict_surjective]
    exact (Subgroup.map_eq_bot_iff _).mpr (by simpa only [MonoidHom.ker_rangeRestrict] using hk)
  obtain ⟨n,hn⟩ := exists_derivedSeries_eq_solvableResidual (G := f.range)
  exact ⟨n,hn.trans hz⟩

theorem source_localAction_twoCore
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : IsOrderingMaximal T M) :
    pCore 2 (internalActionImage M (localModule T M) (le_normalizer_conjugateSpanBy _ _)) = ⊥ := by
  let V := localModule T M
  let f := actionHom M V (le_normalizer_conjugateSpanBy _ _)
  have hred := localModule_reduced_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let := hred.normal
  have hk : f.ker = centralizer (V.subgroupOf M : Set M) := by
    rw [show f.ker = (centralizer (_ : Set G)).subgroupOf M from actionHom_ker M _ _]
    ext m
    constructor
    · intro hm v hv
      exact Subtype.ext (hm v hv)
    · intro hm v hv
      exact congrArg M.subtype (hm ⟨v,localModule_le T hM.1.2 hv⟩ hv)
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivRange f)
  change pCore 2 f.range = ⊥
  rw [←pCore_map_iso 2 e,hred.quotient_pCore_eq_bot,Subgroup.map_bot]

/-- The actual minimum actor moves an odd prime core at three or five. -/
theorem source_centralizing_minimumActor
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let D := internalActionImage M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    ∃ A : Subgroup D, A ∈ QhatStar ρ ∧
      ∃ p : ℕ, (p = 3 ∨ p = 5) ∧ ⁅pCore p D,A⁆ ≠ ⊥ := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let D := internalActionImage M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  let := source_localAction_isSolvable hG T hempty hM
  have hcore := source_localAction_twoCore hG T hM
  obtain ⟨A,hA⟩ := (QhatStar_nonempty_iff ρ).mpr
    (source_centralizing_cubicRatio_le_two hG T hempty hM hmany hJ)
  let := hA.1.2.1.2
  obtain ⟨p,hp,hodd,hmove⟩ := exists_odd_primeCore_nontrivial_action
    (generalizedFitting_eq_fitting_of_solvable D) hcore A
    (IsElementaryAbelian.isPGroup 2 A) hA.1.2.1.1
  let := Fact.mk hp
  exact ⟨A,hA,p,(source_lemma_D_2_13_one_two ρ
    (imageRepresentation_injective _ _ _) hA hodd hmove).1,hmove⟩

/-- The literal actual M cover supplies the noncyclic D.2 source input. -/
theorem source_localAction_noncyclic_ratio
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let D := internalActionImage M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    ∀ A : Subgroup D, A ∈ QhatStar ρ → 1 < rank A →
      subspaceCommutator ρ ⊤ (fittingSubgroup D) = ⊤ →
      fixedCodim ρ A = 3 ∧ cubicRatio ρ = 3 / 2 ∧
        ∀ B ∈ QhatStar ρ, 1 < rank B := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let f := actionHom M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  let := source_localAction_isSolvable hG T hempty hM
  dsimp only
  intro A hA hr hmoved
  exact SourceReduction.solvable_source_ratio_and_noncyclic ρ
    (Chapter3.sqtk_of_mem_H hG (Chapter1.mem_H_of_isTwoLocal hM.1.1.1))
    f.rangeRestrict f.rangeRestrict_surjective (imageRepresentation_injective _ _ _) hA hr
    (source_localAction_twoCore hG T hM) hmoved
end CFSG.Quasithin.Chapter15.Section01
