module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource.ProjectiveTwoFour
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource.SpecialLinearFour

/-!
# Containment for every original higher-field component

The source exclusions leave PSL₂(4) and full SL₃(4). Both now contain L₁;
the actual generated-overgroup identity gives H=KT, and propagation of the
source seed commutator gives U_H=[U_H,K]. The unrestricted-overgroup
application reduces internally to KL₁T while preserving the intrinsic
component quotient and the original local marks. In the PSL₂(4) case the
local quotient must be ordinary A₆.

These discharge the containment paragraph of 13.8.20. The two surviving
terminal contradictions, whole-quotient binary exclusion and final source
assembly remain with qt-d-138-fields-source. Earlier original premises
retain their producers through qt-d-1381-source.
Source: Aschbacher–Smith, 13.8.20–21, printed pp.954–957.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- All surviving higher-field components contain L₁, generate H with T,
and move the whole U_H. The two remaining model contradictions are separate. -/
theorem source_higher_field_reduction
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (hfield : HigherFieldAlternative (K ⧸ pCore 2 K)) :
    one L T V₁ ≤ K ∧ H = K ⊔ (T : Subgroup G) ∧
      Source.UH H V₃ = ⁅Source.UH H V₃,K⁆ := by
  rcases source_higher_field_linear_list c hfield with hm | hm
  · obtain ⟨hLK,_,hHT,hU,_⟩ := source_projectiveTwo_four_reduction c hm
    exact ⟨hLK,hHT,hU⟩
  · exact source_specialLinearThree_four_reduction c hm

/-- For any component of an unrestricted original overgroup, the full
higher-field catalogue now forces containment of L₁ in that component. -/
theorem original_higher_field_containment
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9 : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hfield : HigherFieldAlternative (K ⧸ pCore 2 K)) : one L T V₁ ≤ K := by
  let c := Overgroups.context_of_original d h hF9 hcentral hcomm hH
  exact (source_higher_field_reduction (Overgroups.reducedContext c K hKH hK) hfield).1

/-- The original PSL₂(4) component also forces the ordinary A₆ local
quotient; the intrinsic K/O₂(K) marking survives reduction to KL₁T. -/
theorem original_projectiveTwo_four_containment
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9 : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4) :
    one L T V₁ ≤ K ∧ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) := by
  let c := Overgroups.context_of_original d h hF9 hcentral hcomm hH
  have hr := source_projectiveTwo_four_reduction (Overgroups.reducedContext c K hKH hK) hm
  exact ⟨hr.1,hr.2.1⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
