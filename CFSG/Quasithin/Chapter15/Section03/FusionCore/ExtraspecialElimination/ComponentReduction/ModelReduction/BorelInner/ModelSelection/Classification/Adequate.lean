module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelSelection.Classification
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.Adequate.Components
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.ExhaustiveSource

/-!
# Selected components from the corrected adequate B.5 classification

The actual perfect star actor excludes the group-only outer configuration.
For quasisimple F*, the selected C-component is F* itself; the corrected
projective-line action gives exactly the same concrete component model.
All other cases reuse the full preserved product and module records.

The literal SourceSetup application keeps its section representation,
relative component and two-core quotient equivalence. The universal B.5
implication is still an explicit earlier-source input.
Source: Aschbacher–Smith, B.5.1/B.5.6, pp.99–105; 15.3.49(i)–(k),
pp.1143–1144 (combined manuscript, 1 March 2004).
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open FFAlternatives
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelSelection.Classification

/-- The selected C-component retains its original quasisimplicity and
concrete carrier conclusion under the corrected adequate alternatives. -/
theorem component_classification_of_adequate
    {D V : Type*} [Group D] [Finite D] [Group.IsPerfect D]
    [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) D V)
    (h : ProjectiveLine.AdequateSourceAlternative ρ)
    {C : Subgroup D} (hC : C.IsCComponent) : IsQuasisimple C ∧ ComponentModel C := by
  cases h with
  | trivial ht => exact component_classification_of_source_alternative ρ (.trivial ht) hC
  | quasisimple hq actions =>
    have hf : IsComponent D (generalizedFitting D) :=
      ⟨(inferInstance : (generalizedFitting D).Normal).isSubnormal, hq⟩
    have he : C = generalizedFitting D := by
      rcases hf.subnormal_dichotomy C hC.subnormal with hle | hcomm
      · exact (hf.isCComponent.eq_of_le hC hle).symm
      · rw [commutator_comm, commutator_eq_bot_iff_le_centralizer] at hcomm
        exact hC.eq_of_le hf.isCComponent
          (hcomm.trans ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le)
    rw [he]
    let := hq
    exact ⟨hq, componentModel_of_quasisimpleModel (actions.fittingModel ρ)⟩
  | symmetricThree c =>
    exact component_classification_of_source_alternative ρ (.symmetricThree c) hC
  | twoFactors c => exact component_classification_of_source_alternative ρ (.twoFactors c) hC
  | outerSixThree c => exact (outerSixThreeShape_not_perfect c).elim
  | hyperplane c => exact component_classification_of_source_alternative ρ (.hyperplane c) hC

universe u
variable {G : Type u} [Group G] [Finite G]
variable {κ : GroupClass.{u}} {H M Y V Y0 L ZS Z A : Subgroup G}
    {T : Sylow 2 G} [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : SourceSetup κ H M Y V Y0 L ZS Z A T)

include d

/-- Apply the complete universal classification to the literal faithful
section action. All representation clauses remain available to consumers. -/
theorem sourceSetup_alternative_of_adequate (h : ProjectiveLine.AdequateGeneralClassificationInput.{u,u} κ) :
    ProjectiveLine.AdequateSourceAlternative (d.action.representation.comp (starImage H (localSpan A H)).subtype) := by
  have hyp := BinaryModels.ModelSieve.starSpanFFHypothesis
    H ZS Z A d.action d.sqtk d.actor_le d.best
  exact h _ _ _ hyp.1

/-- The selected component has its intrinsic quasisimple two-core quotient
and one of the actual B.5.5(1iv) carriers. Component generation, not an
additional quasisimplicity assumption, supplies the perfect FF actor. -/
theorem sourceSetup_component_classification_of_adequate (h : ProjectiveLine.AdequateGeneralClassificationInput.{u,u} κ) :
    IsQuasisimple (L ⧸ pCore 2 L) ∧ ComponentModel (starImage H L) := by
  let : Group.IsPerfect (starImage H (localSpan A H)) :=
    BinaryModels.ModelSieve.starSpan_isPerfect H A d.actor_le d.component_generation
  obtain ⟨hq, hm⟩ := component_classification_of_adequate _
    (sourceSetup_alternative_of_adequate d h) (star_isCComponent_in_span d)
  let e := subgroupOfEquivOfLe
    (show starImage H L ≤ starImage H (localSpan A H) from
      map_mono (comap_mono d.component_le))
  let := hq
  have hstar : IsQuasisimple (starImage H L) := IsQuasisimple.of_mulEquiv e
  exact ⟨(component_quotient_quasisimple_iff d).mpr hstar,
    componentModel_of_equiv e.symm hm⟩

/-- The intrinsic quotient part of the classification. -/
theorem sourceSetup_component_quotient_quasisimple_of_adequate (h : ProjectiveLine.AdequateGeneralClassificationInput.{u,u} κ) :
    IsQuasisimple (L ⧸ pCore 2 L) := (sourceSetup_component_classification_of_adequate d h).1


end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelSelection.Classification
