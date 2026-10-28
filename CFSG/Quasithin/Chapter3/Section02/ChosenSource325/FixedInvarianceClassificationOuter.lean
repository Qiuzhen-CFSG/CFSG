module

public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.FixedInvarianceClassification
public import CFSG.Quasithin.ChapterB.Section05.OuterSixThreeShape.Residual

/-!
# The outer branch and the complete fixed-component implication

For a high-three-rank component, the original B.5.7 cover construction
either supplies quasisimple Fitting or a noncentral cubic core. In the latter
case its marked moved-module calculation makes that core fix [W,X].
Full movement and faithfulness force the core to be trivial, a contradiction.
Thus no disputed whole-module splitting is needed. In the outer group
configuration perfectness identifies the original component with its A₆
factor, to which this high-rank argument applies. The complete adequate B.5
classification and the ordinary exclusions now prove FixedComponentInput.

Source: Aschbacher--Smith B.5.7, p.106, and D.3.20, p.204.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open ChapterB ChapterB.SourceInduction ChapterB.QuasisimpleSource
open HighThreeRank HighThreeRank.CoverCentralizer.SourceConstruction
open HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison
universe u v
variable {H : Type u} [Group H] [Finite H]
  {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) H W)

/-- Full movement removes the noncentral cubic-core branch of B.5.7. -/
theorem quasisimple_fitting_of_full_high_rank
    (h : FFHypothesis KnownSimple.IsKnownSimple ρ) {X : Subgroup H}
    (hX : IsComponent H X) (hr : 1 < primeRank 3 X) (hm : moved ρ X = ⊤) :
    IsQuasisimple (generalizedFitting H) ∧
      Nonempty (ProjectiveLine.QuasisimpleSourceConclusion ρ (generalizedFitting H)) := by
  let hA : SemisimpleInput.{u} KnownSimple.IsKnownSimple :=
    fun _ _ _ => ChapterA.Section02.theoremA_knownSimple
  let h36 : Chapter1.Section02.A36Input.{u} KnownSimple.IsKnownSimple :=
    ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  let h4 : ProjectiveLine.IrreducibleClassificationInput.{u,v} KnownSimple.IsKnownSimple :=
    SourceClassification.irreducibleClassification_knownSimple
  let h1 : ProjectiveLine.QuasisimpleClassificationInput.{u,v} KnownSimple.IsKnownSimple :=
    SourceCompletion.knownSimple_quasisimpleClassificationInput hA h36 h4 nonbinaryG2RootPairInput
  obtain ⟨d⟩ := PreciseMultiplierInputs.liftedCover_of_preparation ρ
    (coverInput_of_a36 h36)
    (PreparationSource.componentInput_of_classification_sources hA h36 h4) hA h36 h hX hr
  rcases HighThreeRank.CoverCentralizer.reduction_of_liftedCover h hX hr d with
      ⟨hsq, hfit⟩ | hd
  · exact HighThreeRank.quasisimple_branch ρ h1 h hX hsq hfit
  · obtain ⟨d⟩ := hd
    obtain ⟨A, hAf, hmove, _, _⟩ := HighThreeRank.exists_moving_offender ρ h hX d
    obtain ⟨r⟩ := reduced_of_threeFreePerfectKernels h1
      alternatingEight_threeFreePerfectKernels binaryG2_threeFreePerfectKernels
      ρ h hX hr d hAf hmove
    obtain ⟨m⟩ := ModuleCalculation.NaturalReduction.model_of_reduced ρ h hX d hmove r
    have hf := ModuleCalculation.NaturalCentralizers.threeCore_fixes_model ρ
      ModuleCalculation.NaturalCentralizers.ConcreteModels.modelCommutants hX d m
    have hz : pCore 3 H = ⊥ := by
      apply (Subgroup.eq_bot_iff_forall _).mpr
      intro g hg
      apply h.faithful
      ext v
      simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, map_one, Module.End.one_apply] using
        hf (hm.symm ▸ (Submodule.mem_top (x := v))) ⟨g, hg⟩
    exact (d.noncentral (hz ▸ bot_le)).elim

/-- The literal outer group configuration is excluded on a fully moved module. -/
theorem not_outerSixThree_of_full_component
    (h : FFHypothesis KnownSimple.IsKnownSimple ρ) {X : Subgroup H}
    (hX : IsComponent H X) (hm : moved ρ X = ⊤) (c : OuterSixThreeShape H) : False := by
  let := hX.2
  let := c.first_normal
  let := c.quotient_first_solvable
  have he : X = c.first := hX.eq_of_le c.first_isComponent
    (le_of_isPerfect_of_solvable_quotient X c.first)
  have hr : 1 < primeRank 3 X := by rw [he]; exact c.first_three_rank
  exact c.not_quasisimple_fitting (quasisimple_fitting_of_full_high_rank ρ h hX hr hm).1

/-- The exact fixed-component implication, with every B.5 source input discharged. -/
theorem fixedComponentInput_knownSimple : FixedComponentInput.{u,v} := by
  intro H _ _ W _ _ ρ h X hnormal hquasi hm hc
  have hX : IsComponent H X := ⟨hnormal.isSubnormal, hquasi⟩
  let : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).mpr hX.isCComponent.ne_bot
  let : Nontrivial H := X.subtype_injective.nontrivial
  cases nontrivialAdequateAlternative_knownSimple ρ h with
  | quasisimple hq c => exact irrPlus_of_quasisimple_fitting ρ X hX hm hc hq c
  | symmetricThree c =>
    let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
      let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
      apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
      rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]
    let : Group.IsSolvable H := Group.isSolvable_of_isSolvable_injective
      (f := c.equiv.toMonoidHom) c.equiv.injective
    exact (Group.IsPerfect.not_isSolvable X inferInstance).elim
  | twoFactors c => exact (not_twoFactors_of_full_component ρ X hX hm c).elim
  | outerSixThree c => exact (not_outerSixThree_of_full_component ρ h hX hm c).elim
  | hyperplane c => exact (not_hyperplane_of_full_component ρ X hm c).elim

/-- D.3.20 on the original faithful action, with no classification premise. -/
theorem source_seed_eq_top_of_nonzero_fixed
    {H : Type u} [Group H] [Finite H]
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) H W} {T : Sylow 2 H}
    {X : Subgroup H} {I : Submodule (ZMod 2) W}
    (h : FixedSeedHypotheses ρ T X I) : I = ⊤ :=
  source_seed_eq_top_of_fixedComponent fixedComponentInput_knownSimple
    h.toSourceHypotheses h.component h.offender h.fixed

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
