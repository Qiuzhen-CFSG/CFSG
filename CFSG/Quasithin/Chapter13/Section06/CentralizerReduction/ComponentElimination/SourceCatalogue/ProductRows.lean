module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceCatalogue.QuasisimpleRows
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.ModelComparison.Catalogue
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.Adequate.Components
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.SourceB5.Complete
public import Theory.SpecificGroups.PSL3.OddDegreeProjectiveComparison

/-!
# The component catalogue in the remaining B.5.6 rows

An ordinary component of a product is one of its nontrivial quasisimple
residual factors. The proved residual classification identifies these with
binary projective linear groups or A₅. The outer A₆–C₃ extension contributes
only its A₆ factor. These deductions complete the actual component catalogue
for the native adequate B.5.6 classification, preserving the original actor
and component throughout.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.6(3–5),
printed p.105, and the paragraph before 13.6.20, printed p.931.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceCatalogue
open ChapterB.QuasisimpleSource ChapterB.SourceInduction
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence

private theorem model_of_product_component {D : Type*} [Group D]
    (h : ProductComponents.ComponentModel D) : Model D := by
  rcases h with h | e
  · cases h with
    | linear_two F n hn hc e =>
      let B : BinaryField :=
        { Carrier := F
          binaryAlgebra := ZMod.algebra F 2
          degree := n
          degree_pos := by omega
          card_eq := hc }
      exact .linearTwo B e
    | linear_three F n hn ho hc e =>
      let B : BinaryField :=
        { Carrier := F
          binaryAlgebra := ZMod.algebra F 2
          degree := n
          degree_pos := hn
          card_eq := hc }
      exact Model.of_linearThree B (e.some.trans
        (Matrix.PSL3.OddDegreeProjectiveComparison.specialProjectiveEquiv hc ho).symm)
  · exact Model.of_alternatingFive e.some

private theorem factor_residual_catalogue {D : Type*} [Group D] [Finite D]
    (h : FFAlternatives.FactorModel D) :
    solvableResidual D = ⊥ ∨
      (IsQuasisimple (solvableResidual D) ∧ Model (solvableResidual D)) := by
  rcases ProductComponents.factor_residual h with ⟨_,hb⟩ | ⟨hq,hm⟩
  · exact Or.inl hb
  · exact Or.inr ⟨hq,model_of_product_component hm⟩

private theorem model_of_residual_product {D A B : Type*}
    [Group D] [Group A] [Group B] (e : D ≃* A × B)
    (hA : solvableResidual A = ⊥ ∨
      (IsQuasisimple (solvableResidual A) ∧ Model (solvableResidual A)))
    (hB : solvableResidual B = ⊥ ∨
      (IsQuasisimple (solvableResidual B) ∧ Model (solvableResidual B)))
    {C : Subgroup D} (hC : IsComponent D C) : Model C := by
  have heC := (hC.map_equiv e).isCComponent
  rcases cComponent_eq_residual_factor
      (hA.imp_right And.left) (hB.imp_right And.left) heC with he | he
  · rcases hA with hb | ⟨_,hm⟩
    · exact (heC.ne_bot (by simpa only [hb,bot_prod_bot] using he)).elim
    · exact Model.transport
        (((e.subgroupMap C).trans (MulEquiv.subgroupCongr he)).trans residualLeftEquiv).symm hm
  · rcases hB with hb | ⟨_,hm⟩
    · exact (heC.ne_bot (by simpa only [hb,bot_prod_bot] using he)).elim
    · exact Model.transport
        (((e.subgroupMap C).trans (MulEquiv.subgroupCongr he)).trans residualRightEquiv).symm hm

private theorem model_of_product {D A B : Type*}
    [Group D] [Group A] [Finite A] [Group B] [Finite B]
    (e : D ≃* A × B) (hA : FFAlternatives.FactorModel A)
    (hB : FFAlternatives.FactorModel B)
    {C : Subgroup D} (hC : IsComponent D C) : Model C :=
  model_of_residual_product e (factor_residual_catalogue hA)
    (factor_residual_catalogue hB) hC

variable {D V : Type*} [Group D] [Finite D]
  [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V} {C : Subgroup D}

/-- Every actual component in B.5.6(3) belongs to the source catalogue. -/
theorem model_of_twoFactors (c : SourceTwoFactorCase ρ)
    (hC : IsComponent D C) : Model C := by
  let d := FFAlternatives.SourceB5.pair c
  exact model_of_product d.product.equiv.symm
    (d.firstCase.factorModel ρ) (d.secondCase.factorModel ρ) hC

/-- Both second-factor alternatives of B.5.6(5) retain their actual models. -/
theorem model_of_hyperplane (c : HyperplaneCase ρ)
    (hC : IsComponent D C) : Model C := by
  let d := FFAlternatives.SourceB5.hyperplane c
  exact model_of_product d.product.equiv.symm
    (.linearThree FFAlternatives.BinaryField.two (by decide) d.firstEquiv)
    (d.secondCase.factorModel ρ) hC

omit [Finite D] in
/-- The adequate outer extension has the same unique A₆ component. -/
theorem model_of_outerSixThree (c : ChapterB.OuterSixThreeShape D)
    (hC : IsComponent D C) : Model C := by
  have hle := FFAlternatives.outerSixThreeShape_component_le_first c hC
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsQuasisimple (alternatingGroup (Fin 6)) := {
    toIsPerfect := inferInstance
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple c.first := IsQuasisimple.of_mulEquiv c.firstEquiv.symm
  have ht : IsComponent c.first ⊤ :=
    ⟨IsSubnormal.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩
  have he : C = c.first := le_antisymm hle
    (subgroupOf_eq_top.mp ((hC.subgroupOf hle).eq_of_le ht le_top))
  exact Model.of_alternatingSix ((MulEquiv.subgroupCongr he).trans c.firstEquiv)

/-- The complete native B.5.6 alternatives supply the exact component
catalogue needed before the original field exclusions in 13.6.18–19. -/
theorem model_of_adequate_alternative (h : AdequateAlternative ρ)
    (hC : IsComponent D C) : Model C := by
  rcases h with ht | h
  · let := ht
    exact (hC.isCComponent.ne_bot (Subsingleton.elim _ _)).elim
  cases h with
  | quasisimple hq ha =>
    have hf : IsComponent D (generalizedFitting D) :=
      ⟨(inferInstance : (generalizedFitting D).Normal).isSubnormal,hq⟩
    have he := hC.eq_of_le hf (component_le_generalizedFitting D C hC)
    let := hq
    exact Model.transport (MulEquiv.subgroupCongr he).symm (model_of_quasisimple ha)
  | symmetricThree c =>
    let := hC.2
    let : Nontrivial C := (nontrivial_iff_ne_bot C).mpr hC.isCComponent.ne_bot
    let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
    let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
      apply Group.isSolvable_of_ker_le_range
        (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
      rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]
    let : Group.IsSolvable D := Group.isSolvable_of_isSolvable_injective
      (f := c.equiv.toMonoidHom) c.equiv.injective
    exact (Group.IsPerfect.not_isSolvable C inferInstance).elim
  | twoFactors c => exact model_of_twoFactors c hC
  | outerSixThree c => exact model_of_outerSixThree c hC
  | hyperplane c => exact model_of_hyperplane c hC

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceCatalogue
