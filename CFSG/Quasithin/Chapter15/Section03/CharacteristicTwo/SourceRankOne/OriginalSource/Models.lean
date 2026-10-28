module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.Components
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.ModelComparison.Catalogue
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.ModelComparison.SourceTransport

/-!
# The actual component catalogue in the corrected rank-one source action

The corrected adequate B.5 theorem classifies the genuine Thompson action.
Every ordinary component has one of its FF models; the outer case needs only
the normal product and cyclic quotient of the specified A₆–C₃ configuration.
The model is transported through the literal component subgroup inclusion.
This supplies the B.5 premise in15.3.27's orbit and placement comparisons.

Source: Aschbacher–Smith B.5.6 and15.3.27, printed pp.105,1130–1131.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open RankOneConfiguration.Parabolics.Placement.ModelComparison
open Catalogue
variable {D : Type*} [Group D]
private theorem residual_model_of_quasisimple [IsQuasisimple D]
    (h : QuasisimpleModel D) :
    IsQuasisimple (solvableResidual D) ∧ QuasisimpleModel (solvableResidual D) := by
  let e : solvableResidual D ≃* D :=
    (MulEquiv.subgroupCongr solvableResidual_eq_top).trans topEquiv
  exact ⟨IsQuasisimple.of_mulEquiv e.symm, quasisimpleModel_of_equiv e h⟩

private theorem alternatingSix_quasisimple : IsQuasisimple (alternatingGroup (Fin 6)) where
  toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  simple := by
    let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    exact ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

/-- The outer A₆ × C₃ extension contributes only its A₆ component. The cyclic
quotient first places the component in the actual normal product. -/
theorem outerSixThree_component_model (c : ChapterB.OuterSixThreeShape D)
    {C : Subgroup D} (hC : IsComponent D C) : QuasisimpleModel C := by
  let := hC.2
  let := outerSixThreeShape_product_normal c
  let := outerSixThreeShape_quotient_isCyclic c
  let : CommGroup (D ⧸ (c.first ⊔ c.second)) := IsCyclic.commGroup
  have hCN : C ≤ c.first ⊔ c.second :=
    le_of_isPerfect_of_solvable_quotient C (c.first ⊔ c.second)
  let := alternatingSix_quasisimple
  let : IsQuasisimple c.first := IsQuasisimple.of_mulEquiv c.firstEquiv.symm
  let : Group.IsSolvable c.second := Group.isSolvable_of_isSolvable_injective
    (f := c.secondEquiv.toMonoidHom) c.secondEquiv.injective
  have hm := component_model_of_residual_product c.product.symm
    (Or.inr (residual_model_of_quasisimple (.alternatingSix c.firstEquiv)))
    (Or.inl (solvableResidual_eq_bot (G := c.second))) (hC.subgroupOf hCN)
  exact quasisimpleModel_of_equiv (subgroupOfEquivOfLe hCN).symm hm

private theorem symmetricThree_solvable : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  apply Group.isSolvable_of_ker_le_range
    (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
  rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]

/-- Extract the model of every ordinary component from the complete source
alternatives. The actor need not be perfect, and no FF witness or universal
classification implication is assumed beyond the explicit alternative. -/
theorem component_model_of_adequate_alternative [Finite D]
    (h : ProjectiveLine.AdequateSourceAlternative ρ) {C : Subgroup D} (hC : IsComponent D C) :
    QuasisimpleModel C := by
  cases h with
  | trivial ht =>
    let := ht
    exact (hC.isCComponent.ne_bot (Subsingleton.elim _ _)).elim
  | quasisimple hq ha =>
    have hf : IsComponent D (generalizedFitting D) :=
      ⟨(inferInstance : (generalizedFitting D).Normal).isSubnormal, hq⟩
    have he := hC.eq_of_le hf (component_le_generalizedFitting D C hC)
    exact quasisimpleModel_of_equiv (MulEquiv.subgroupCongr he) (ha.fittingModel ρ)
  | symmetricThree c =>
    let := hC.2
    let : Nontrivial C := (nontrivial_iff_ne_bot C).mpr hC.isCComponent.ne_bot
    let := symmetricThree_solvable
    let : Group.IsSolvable D := Group.isSolvable_of_isSolvable_injective
      (f := c.equiv.toMonoidHom) c.equiv.injective
    exact (Group.IsPerfect.not_isSolvable C inferInstance).elim
  | twoFactors c =>
    exact component_model_of_product c.product.equiv.symm
      (c.firstCase.factorModel ρ) (c.secondCase.factorModel ρ) hC
  | outerSixThree c => exact outerSixThree_component_model c hC
  | hyperplane c =>
    exact component_model_of_product c.product.equiv.symm
      (.linearThree BinaryField.two (by decide) c.firstEquiv) (c.secondCase.factorModel ρ) hC


/-- The proved corrected classifier applies to the original Thompson component. -/
theorem component_star_ff_model
    {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I) (hS : Chapter1.IsSylowIn 2 d.S I) :
    QuasisimpleModel (d.starImage I c.L) := by
  have hVT := d.action.le_sylow d.T d.sylow_le (localModule_le d.T d.sylow_le)
  obtain ⟨hZI,hU,hyp,hcomp⟩ := thompson_source_inputs d
    (OutsideStructure.outside_sqtk hG d hI) hVT hS hf c
  let _ := hU
  have hmodel := component_model_of_adequate_alternative _
    (SourceB5.classification.general _ _ _ hyp) hcomp
  exact quasisimpleModel_of_equiv (componentThompsonEquiv d c).symm hmodel

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
