module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource.SpecialLinearFourTerminal
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource.SixComplete
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.Overgroups.OriginalSource

/-!
# Applying the completed field and cover exclusions

The higher-field contradiction discharges the last premise of the proved
small-cover sieve. The actual component catalogue therefore gives L₁≤K,
the remaining quotient list, H=KT and U_H=[U_H,K]. Reduction to KL₁T and
lifting through the literal quotient extend these conclusions to every
component of every unrestricted original overgroup; H=KT is stated as the
actual set product there.

The binary component PSL₃(2) remains in the list. Only the exclusion of the
whole quotient H/O₂(H)≃PSL₃(2), namely 13.8.19, remains explicit in the
ComponentConclusions and linear GroupFacts applications. Discharging that
binary premise stays with qt-d-138-fields-source. The preceding component
source retains qt-d-138-components-source, and qt-d-1381-source owns final
discharge of the original LocalSetup, maximality and earlier F.9 inputs.
These conditional last applications do not assert the full 13.8.19–21 assembly.

Source: Aschbacher–Smith, 13.8.20–21, printed pp.954–957.
-/

public section
open Subgroup Representation Representation.BinaryOffender

open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- The field and cover sieve now gives the actual nonbinary conclusions
of 13.8.21, including the surviving component PSL₃(2) row. -/
theorem source_component_consequences
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K) :
    one L T V₁ ≤ K ∧ RemainingQuotient (K ⧸ pCore 2 K) ∧
      H = K ⊔ (T : Subgroup G) ∧ Source.UH H V₃ = ⁅Source.UH H V₃,K⁆ :=
  SmallCovers.OriginalSource.source_consequences_of_field_exclusion c (source_no_higher_field c)

/-- On every unrestricted original overgroup, construct containment, the
remaining quotient list, the actual set product and full commutator generation. -/
theorem original_component_consequences
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9 : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) :
    one L T V₁ ≤ K ∧ RemainingQuotient (K ⧸ pCore 2 K) ∧
      (H : Set G) = (K : Set G) * (T : Set G) ∧
      Source.UH H V₃ = ⁅Source.UH H V₃,K⁆ :=
  Overgroups.original_consequences d h hF9 hcentral hcomm
    (fun c => source_no_higher_field c) hH hKH hK

variable
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9 : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (binary : ∀ {J C : Subgroup G}, SourceContext T L V V₁ V₂ V₃ M G₁ J C →
      ¬ Nonempty (Source.Hstar J ≃* Matrix.PSL3Two.PSL))

include d h hF9 hcentral hcomm binary

/-- Only the original whole-quotient exclusion 13.8.19 remains in the field
owner's input to the linear sieve. Its binary premise is still to be discharged. -/
theorem original_component_conclusions_of_binary :
    AlternatingAndLinear.LinearReduction.OriginalSource.ComponentConclusions (one L T V₁) T G₁ M :=
  Overgroups.original_component_conclusions d h hF9 hcentral hcomm
    (fun c => source_no_higher_field c) binary

/-- Apply the completed field sieve to the literal linear-group consumer,
retaining only the undischarged whole-quotient binary exclusion as an extra premise. -/
theorem original_linear_group_facts_of_binary :
    AlternatingAndLinear.LinearReduction.SourceReduction.GroupFacts L (one L T V₁) T V V₁ V₃ G₁ M :=
  Overgroups.original_linear_group_facts d h hF9 hcentral hcomm
    (fun c => source_no_higher_field c) binary
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
