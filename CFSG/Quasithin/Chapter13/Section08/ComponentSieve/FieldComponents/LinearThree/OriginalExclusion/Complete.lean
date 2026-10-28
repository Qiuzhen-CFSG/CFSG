module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion.MiddleResidue
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion.Assembly

/-!
# Completing the original field and cover sieve

The actual chamber, middle quotient and all three rank-two residues now
construct the C₃ system in the original abelian-span branch. I.5 forces
Z(H) = 1 in that same H, contradicting its original central line V₁. This
excludes the whole quotient L₃(2), and discharges OrdinaryNaturalThreeExclusion.

Combined with the proved higher-field and small-cover exclusions, this
supplies ComponentConclusions and the literal linear GroupFacts on every
original overgroup. The component L₃(2) remains allowed, with whole quotient
Aut(L₃(2)); containment, the remaining quotient list, H = KT and
U_H = [U_H,K] are retained. The commutator conclusion is also exported by
HigherFieldReduction.OriginalSource.original_component_consequences.

No field, cover, residue, component catalogue or natural-module exclusion
is an extra premise of these applications. The genuine preceding LocalSetup,
Hypothesis1221, F.9 applicability, centralizer containment and core
noncentrality remain explicit, with final earlier-source discharge owned by
qt-d-1381-source and its existing producers.
Source: Aschbacher–Smith 13.8.19–21, printed pp.953–957.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- All local residues of the literal C₃ family are constructed in the original abelian-span branch. -/
theorem source_binary_exclusion
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K) :
    ¬ Nonempty (Source.Hstar H ≃* Matrix.PSL3Two.PSL) := by
  let := c.localSetup.uh_elementary c.component.local_overgroup
  have h := c.f9 H c.component.local_overgroup
  let act := Comparison.conjugationAction (c.localSetup.line_le_uh H) h.plus_le_H
    (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    h.commutator_UH_QH_le_point
  rintro ⟨e₀⟩
  obtain ⟨eJ⟩ := source_binary_middle_quotient c act e₀
  exact source_binary_false_of_residues c act e₀ (source_binary_chamber c e₀) eJ
    (source_binary_family_point_parabolics c e₀)
    (source_binary_family_middle_parabolics c act e₀)
    (source_binary_family_plane_parabolics c act e₀)

/-- Discharge the remaining ordinary-natural-three interface without any extra local premise. -/
theorem ordinary_natural_three_exclusion : OrdinaryNaturalThreeExclusion T L V V₁ V₂ V₃ M G₁ := by
  intro H K c _ act e _ _
  exact source_binary_exclusion c ⟨e.trans Matrix.PSL3Two.equiv⟩

variable
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9 : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
include d h hF9 hcentral hcomm

/-- Original 13.8.19 for every original overgroup, with its component selected
from the preceding source rather than supplied as an extra hypothesis. -/
theorem original_binary_exclusion
    (hH : H ∈ Source.Hz (one L T V₁) T G₁ M) :
    ¬ Nonempty (Source.Hstar H ≃* Matrix.PSL3Two.PSL) := by
  obtain ⟨K,hKH,hK,_⟩ := Components.original_exists_normal_component
    d h hF9 hcentral hcomm hH
  let a := Overgroups.context_of_original d h hF9 hcentral hcomm hH
  have hf (C : Subgroup G) (hCH : C ≤ H) (hC : (C.subgroupOf H).IsCComponent) :=
    HigherFieldReduction.OriginalSource.source_no_higher_field
      (Overgroups.reducedContext a C hCH hC)
  exact source_binary_exclusion (Overgroups.originalContext a hf K hKH hK)

/-- Original 13.8.19–21 on every original overgroup, with all field and cover exclusions discharged. -/
theorem original_component_conclusions :
    AlternatingAndLinear.LinearReduction.OriginalSource.ComponentConclusions
      (one L T V₁) T G₁ M :=
  HigherFieldReduction.OriginalSource.original_component_conclusions_of_binary
    d h hF9 hcentral hcomm (fun c => source_binary_exclusion c)

/-- Apply the completed sieve to the original linear branch, preserving the allowed binary component. -/
theorem original_linear_group_facts :
    AlternatingAndLinear.LinearReduction.SourceReduction.GroupFacts
      L (one L T V₁) T V V₁ V₃ G₁ M :=
  HigherFieldReduction.OriginalSource.original_linear_group_facts_of_binary
    d h hF9 hcentral hcomm (fun c => source_binary_exclusion c)
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion
