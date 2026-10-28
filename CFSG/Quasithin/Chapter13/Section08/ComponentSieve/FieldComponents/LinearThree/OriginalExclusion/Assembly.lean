module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion.NaturalReduction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource.FieldSieve

/-!
# The covered field sieve and the remaining ordinary natural-three case

The whole binary quotient would force the local A₆ quotient to be ordinary.
Thus the covered local branch now supplies the actual ComponentConclusions
and linear GroupFacts, using the completed higher-field and small-cover
exclusions. These applications retain the preceding original LocalSetup,
maximality, F.9, centralizer and core hypotheses.

For the ordinary branch the remaining contract is only the exclusion of the
literal natural three-space with its original line parabolic. The five H.6.5
alternatives, transvection existence, involution and dimension bounds, covered
local exclusion, and every other field row are proved inputs. The applications
with this last premise are conditional: qt-d-138-fields-source still owns its
discharge and final 13.8.19–21 assembly. The preceding component source retains
qt-d-138-components-source; qt-d-1381-source supplies the original earlier
hypotheses. In particular, the nonabelian-V_H specialization of 13.7.6 in
Section07/OrdinarySource/LinearThreeExclusion cannot supply this abelian case.

Source: Aschbacher–Smith, 13.7.6(1), printed pp.938–940, and 13.8.19–21,
printed pp.953–957 (combined manuscript, 1 March 2004).
-/

@[expose] public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]

/-- The sole remaining ordinary branch: exclude the natural three-dimensional
whole action with the same isomorphism marking L₁T. This is an unproved earlier
source obligation, not a record of the desired component conclusions. -/
def OrdinaryNaturalThreeExclusion
    (T : Sylow 2 G) (L V V₁ V₂ V₃ M G₁ : Subgroup G) : Prop :=
  ∀ {H K : Subgroup G} (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K),
    letI := c.localSetup.uh_elementary c.component.local_overgroup
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
    ∀ (act : SourceAction H V₃ V₁) (e : Source.Hstar H ≃* BinaryLinearThree.Group),
      (Source.starImage H (one L T V₁ ⊔ (T : Subgroup G))).map e.toMonoidHom =
        Matrix.PSL3Two.lineParabolicSL →
      ¬ Nonempty (Representation.Equiv (act.representation.comp e.symm.toMonoidHom) BinaryLinearThree.W)

variable {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- The literal binary exclusion from just the remaining ordinary natural
case. All transvection and H.6.5 classification premises are discharged. -/
theorem source_binary_exclusion_of_natural_three
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (hnatural : OrdinaryNaturalThreeExclusion T L V V₁ V₂ V₃ M G₁) :
    ¬ Nonempty (Source.Hstar H ≃* Matrix.PSL3Two.PSL) := by
  let := c.localSetup.uh_elementary c.component.local_overgroup
  have hF9 := c.f9 H c.component.local_overgroup
  let act := Comparison.conjugationAction (c.localSetup.line_le_uh H) hF9.plus_le_H
    (hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    hF9.commutator_UH_QH_le_point
  rintro ⟨e₀⟩
  obtain ⟨e,hmodel,hmark⟩ := source_binary_marked_natural c act e₀
  exact hnatural c (source_binary_local_ordinary c e₀) act e hmark hmodel

variable
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9 : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
include d h hF9 hcentral hcomm

/-- Complete field-sieve input for every original overgroup in the covered
local branch. No field, cover, binary or containment exclusion is assumed. -/
theorem original_component_conclusions_of_covered
    (hcover : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)) :
    AlternatingAndLinear.LinearReduction.OriginalSource.ComponentConclusions
      (one L T V₁) T G₁ M :=
  HigherFieldReduction.OriginalSource.original_component_conclusions_of_binary
    d h hF9 hcentral hcomm (fun c => source_binary_covered_exclusion c hcover)

/-- Apply the completed covered branch to the literal linear-sieve group
facts, including the allowed binary component's full automorphism quotient. -/
theorem original_linear_group_facts_of_covered
    (hcover : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)) :
    AlternatingAndLinear.LinearReduction.SourceReduction.GroupFacts
      L (one L T V₁) T V V₁ V₃ G₁ M :=
  HigherFieldReduction.OriginalSource.original_linear_group_facts_of_binary
    d h hF9 hcentral hcomm (fun c => source_binary_covered_exclusion c hcover)

/-- The remaining ordinary natural-three proof suffices for the actual
ComponentConclusions. This theorem retains that explicit, undischarged premise. -/
theorem original_component_conclusions_of_natural_three
    (hnatural : OrdinaryNaturalThreeExclusion T L V V₁ V₂ V₃ M G₁) :
    AlternatingAndLinear.LinearReduction.OriginalSource.ComponentConclusions
      (one L T V₁) T G₁ M :=
  HigherFieldReduction.OriginalSource.original_component_conclusions_of_binary
    d h hF9 hcentral hcomm (fun c => source_binary_exclusion_of_natural_three c hnatural)

/-- The same reduced ordinary obligation feeds the actual linear-group
consumer; the final field owner must still prove the natural-three exclusion. -/
theorem original_linear_group_facts_of_natural_three
    (hnatural : OrdinaryNaturalThreeExclusion T L V V₁ V₂ V₃ M G₁) :
    AlternatingAndLinear.LinearReduction.SourceReduction.GroupFacts
      L (one L T V₁) T V V₁ V₃ G₁ M :=
  HigherFieldReduction.OriginalSource.original_linear_group_facts_of_binary
    d h hF9 hcentral hcomm (fun c => source_binary_exclusion_of_natural_three c hnatural)
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion
