module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.ModelComparison.Catalogue.ResidualCarriers
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.SourceAlternatives
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.GroupCore
public import Theory.GroupTheory.CComponent.QuasisimpleFactors

/-!
# Every ordinary component in the full FF alternatives

When F* is quasisimple, component containment identifies the selected
component with F*. For a direct product, the component calculus identifies
it with an embedded quasisimple solvable residual. In the outer A₆ × C₃
case, the cyclic quotient places the perfect component in the normal
product, whose only nontrivial residual factor is A₆. The trivial and S₃
actors have no components. These arguments cover all six constructors,
including both product cases and their binary degree-one endpoints.

`SourceAlternative` remains an explicit conditional input. This module
extracts its component catalogue; the parent supplies the genuine Thompson
action and source classification. No ambient perfectness is required.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1 with its
preceding hypotheses, printed p.99, and B.5.3–6, printed pp.104–105; used
in the model comparison for 15.3.27(2), printed p.1131.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.ModelComparison.Catalogue

variable {D E : Type*} [Group D] [Group E]
variable {A B : Type*} [Group A] [Group B]

/-- A component of an actual product is one of its nontrivial quasisimple
residual factors. Only the component is assumed perfect. -/
theorem component_model_of_residual_product (e : D ≃* A × B)
    (hA : solvableResidual A = ⊥ ∨
      (IsQuasisimple (solvableResidual A) ∧ QuasisimpleModel (solvableResidual A)))
    (hB : solvableResidual B = ⊥ ∨
      (IsQuasisimple (solvableResidual B) ∧ QuasisimpleModel (solvableResidual B)))
    {C : Subgroup D} (hC : IsComponent D C) : QuasisimpleModel C := by
  have hCe := (hC.map_equiv e).isCComponent
  rcases cComponent_eq_residual_factor
      (hA.imp_right And.left) (hB.imp_right And.left) hCe with he | he
  · rcases hA with hb | ⟨_, hm⟩
    · exact (hCe.ne_bot (by simpa only [hb, bot_prod_bot] using he)).elim
    · exact quasisimpleModel_of_equiv
        (((e.subgroupMap C).trans (MulEquiv.subgroupCongr he)).trans residualLeftEquiv) hm
  · rcases hB with hb | ⟨_, hm⟩
    · exact (hCe.ne_bot (by simpa only [hb, bot_prod_bot] using he)).elim
    · exact quasisimpleModel_of_equiv
        (((e.subgroupMap C).trans (MulEquiv.subgroupCongr he)).trans residualRightEquiv) hm

/-- All components in either source product alternative have FF models,
including products with solvable factors. -/
theorem component_model_of_product [Finite A] [Finite B]
    (e : D ≃* A × B) (hA : FactorModel A) (hB : FactorModel B)
    {C : Subgroup D} (hC : IsComponent D C) : QuasisimpleModel C :=
  component_model_of_residual_product e (factor_residual_model hA) (factor_residual_model hB) hC

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
theorem outerSixThree_component_model (c : OuterSixThreeCase ρ)
    {C : Subgroup D} (hC : IsComponent D C) : QuasisimpleModel C := by
  let := hC.2
  let := c.product_normal ρ
  let := c.quotient_isCyclic ρ
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
theorem component_model_of_source_alternative [Finite D]
    (h : SourceAlternative ρ) {C : Subgroup D} (hC : IsComponent D C) :
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
  | outerSixThree c => exact outerSixThree_component_model ρ c hC
  | hyperplane c =>
    exact component_model_of_product c.product.equiv.symm
      (.linearThree BinaryField.two (by decide) c.firstEquiv) (c.secondCase.factorModel ρ) hC

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.ModelComparison.Catalogue
