module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.ExchangedSource
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CriticalSource

/-!
# Original component normality and the concrete 13.8.17 catalogue

The original linear-two and linear-three exclusions reduce nonnormality to
Suzuki. The full natural central-section recognitions exclude Suzuki in both
orbit cases. Every relative C-component is therefore normal in its actual
overgroup, and K L₁ T remains in Hz. The normal F.9.18 model list and the
proved cover comparison give the concrete catalogue on K* in H/O₂(H).

The exported original applications discharge the residual 13.3.9 premise,
choose an actual normal component, and supply the field-component geometry
with its required relative normality and quasisimplicity. They retain the
original LocalSetup, maximal-local, F.9 and 13.5.4 hypotheses. Construction of
these earlier inputs remains with qt-d-135-preparation-source and
qt-d-1378-source, and final 13.8.1 assembly with qt-d-1381-source.

Source: Aschbacher--Smith, 13.8.15--18, printed pp.952--953
(combined manuscript of 1 March 2004).
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.Components
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
  (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
  (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
  (hsource : SolvableExclusion.Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
  (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
include d h hF9all hcentral hcomm hsource hH hKH hK

/-- Original 13.8.16(2) on the intrinsic component quotient, in both orbit cases. -/
theorem source_not_suzuki (m : ℕ) (hm : 1 ≤ m) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* SuzukiMatrixGroup m) := by
  rintro ⟨e⟩
  by_cases hn : (K.subgroupOf H).Normal
  · exact source_not_suzuki_of_normal d h hF9all hcentral hcomm hsource hH hKH hK hn m hm ⟨e⟩
  let J := conjugateSpanBy K (T : Subgroup G) ⊔ (one L T V₁ ⊔ (T : Subgroup G))
  obtain ⟨hJ,hJH,hKJ,hK'⟩ := source_generated_overgroup
    d h hF9all hcentral hcomm hsource hH hKH hK
  have hmove : conjugateSpanBy K (T : Subgroup G) ≠ K := by
    intro he
    exact hn (Swapped.normal_of_sylow_span_eq H K T hKH (le_sup_right.trans hH.1.2)
      (SolvableSource.source_component_orbit d hF9all
        (SolvableSource.covered_normalizer_source d h) hcentral hcomm hsource hH K hK) he)
  have hnJ : ¬ (K.subgroupOf J).Normal := fun hnJ => hmove
    (conjugateSpan_eq_of_normal J K T hKJ (le_sup_right.trans hJ.1.2) hnJ)
  exact Suzuki.NaturalSections.source_exchanged_suzuki_impossible d h hF9all hcentral hcomm hsource
    hJ hKJ hK' rfl hnJ (by omega) e

/-- Original 13.8.16(1): normality is relative to the actual overgroup H. -/
theorem source_component_normal : (K.subgroupOf H).Normal := by
  rcases source_normal_or_suzuki d h hF9all hcentral hcomm hsource hH hKH hK with hn | ⟨m,hm,he⟩
  · exact hn
  · exact (source_not_suzuki d h hF9all hcentral hcomm hsource hH hKH hK m hm he).elim

/-- The normal component generates a genuine member K L₁ T of Hz. -/
theorem source_normal_component_overgroup :
    (K.subgroupOf H).Normal ∧ (K ⊔ (one L T V₁ ⊔ (T : Subgroup G))) ∈
      Source.Hz (one L T V₁) T G₁ M := by
  have hn := source_component_normal d h hF9all hcentral hcomm hsource hH hKH hK
  have hJ := (source_generated_overgroup d h hF9all hcentral hcomm hsource hH hKH hK).1
  rw [conjugateSpan_eq_of_normal H K T hKH (le_sup_right.trans hH.1.2) hn] at hJ
  exact ⟨hn,hJ⟩

/-- Original 13.8.17, with actual models on the literal star image and no catalogue premise. -/
theorem source_component_catalogue : Models.ComponentModel (Source.starImage H K) :=
  source_catalogue_of_normal d h hF9all hcentral hcomm hsource hH hKH hK
    (source_component_normal d h hF9all hcentral hcomm hsource hH hKH hK)

omit hsource in
/-- Both Suzuki orbit cases are excluded with the original residual producer applied. -/
theorem original_not_suzuki (m : ℕ) (hm : 1 ≤ m) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* SuzukiMatrixGroup m) :=
  source_not_suzuki d h hF9all hcentral hcomm
    (EarlierResidual.original_source d h) hH hKH hK m hm

omit hsource in
/-- The original relative normality theorem without a 13.3.9 callback. -/
theorem original_component_normal : (K.subgroupOf H).Normal :=
  source_component_normal d h hF9all hcentral hcomm
    (EarlierResidual.original_source d h) hH hKH hK

omit hsource in
/-- The original generated overgroup, with relative normality established. -/
theorem original_normal_component_overgroup :
    (K.subgroupOf H).Normal ∧ (K ⊔ (one L T V₁ ⊔ (T : Subgroup G))) ∈
      Source.Hz (one L T V₁) T G₁ M :=
  source_normal_component_overgroup d h hF9all hcentral hcomm
    (EarlierResidual.original_source d h) hH hKH hK

omit hsource in
/-- The original concrete 13.8.17 catalogue without normality or residual callbacks. -/
theorem original_component_catalogue : Models.ComponentModel (Source.starImage H K) :=
  source_component_catalogue d h hF9all hcentral hcomm
    (EarlierResidual.original_source d h) hH hKH hK
end CFSG.Quasithin.Chapter13.Section08.Components

namespace CFSG.Quasithin.Chapter13.Section08.Components
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ComponentSieve.FieldComponents.HigherFieldReduction
open ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
  (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
  (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
  (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
include d h hF9all hcentral hcomm hH

/-- Choose an actual normal component with its concrete model, and retain K L₁ T in Hz. -/
theorem original_exists_normal_component :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      ¬ K ≤ M ∧ (K.subgroupOf H).Normal ∧ IsQuasisimple (Source.starImage H K) ∧
      Models.ComponentModel (Source.starImage H K) ∧
      (K ⊔ (one L T V₁ ⊔ (T : Subgroup G))) ∈ Source.Hz (one L T V₁) T G₁ M := by
  have hsource := EarlierResidual.original_source d h
  obtain ⟨K,hKH,hK,hout,hqs⟩ := SolvableSource.exists_component_source
    d h hF9all hcentral hcomm hsource hH
  obtain ⟨hn,hJ⟩ := original_normal_component_overgroup d h hF9all hcentral hcomm hH hKH hK
  exact ⟨K,hKH,hK,hout,hn,hqs,
    original_component_catalogue d h hF9all hcentral hcomm hH hKH hK,hJ⟩

/-- The field-component geometry now receives its actual normality and quasisimplicity
from 13.8.16; only the original generated-overgroup and no-transvection conditions remain. -/
theorem original_selected_component_witness
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (one L T V₁ ⊔ (T : Subgroup G)) = H)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
    (hρ : SeedAction.IsConjugation H V₃ V₁ ρ)
    (hno : ∀ g, Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) ≠ 1) :
    Nonempty (CriticalInputs.SelectedWitness L (T : Subgroup G) H V
      (sourceOne L T V₁) V₃ V₁ ρ) := by
  have hn := original_component_normal d h hF9all hcentral hcomm hH hKH hK
  have hgen' : H = K ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)) := by
    rw [conjugateSpan_eq_of_normal H K T hKH (le_sup_right.trans hH.1.2) hn] at hgen
    exact hgen.symm
  exact CriticalSource.exists_selected_witness d hH (hF9all H hH) hgen' hK hn
    (SolvableSource.component_fitting_source d h hF9all hcentral hcomm
      (EarlierResidual.original_source d h) hH K hK).2 hcentral hcomm ρ hρ hno

end CFSG.Quasithin.Chapter13.Section08.Components
