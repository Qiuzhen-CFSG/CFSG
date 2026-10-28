module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.OriginalSource
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.OriginalSource
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.SourceModels.OriginalNonnormal
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.SourceModels.Normal
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.EarlierResidual.CoveredNormalizer

/-!
# Original component normality and catalogue reduced to Suzuki

Apply the nonnormal F.9.18 list inside the actual generated overgroup
⟨K^T⟩L₁T. The original linear-two and linear-three contradictions leave
only a genuine Suzuki quotient when K is nonnormal. In the normal case,
F.9.18(4) and the concrete cover comparison give the catalogue with Suzuki.
Transport through K/O₂(K) returns that list to the original K* in H*.

These deductions require no assumed component catalogue or branch
elimination. They retain the original earlier 12.2.1, F.9, 13.5.4 and
13.3.9 inputs; the final applications discharge 13.3.9 using its completed
original-source producer. The Suzuki exclusion is still required to establish full
13.8.16 and 13.8.17 and remains with qt-d-138-components-source. The original
setup hypotheses are ultimately discharged by qt-d-1381-source.

Source: Aschbacher--Smith, 13.8.15--17, printed pp.952--953.
-/

public section
open Subgroup Theory.GroupTheory
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

/-- Restriction to the source-generated member of Hz retains the relative component. -/
theorem source_generated_overgroup :
    let J := conjugateSpanBy K (T : Subgroup G) ⊔ (one L T V₁ ⊔ (T : Subgroup G))
    J ∈ Source.Hz (one L T V₁) T G₁ M ∧ J ≤ H ∧ K ≤ J ∧
      (K.subgroupOf J).IsCComponent := by
  dsimp only
  let J := conjugateSpanBy K (T : Subgroup G) ⊔ (one L T V₁ ⊔ (T : Subgroup G))
  have hKJ : K ≤ J := (le_conjugateSpanBy K (T : Subgroup G)).trans le_sup_left
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right.trans le_sup_right
  have hLJ : one L T V₁ ≤ J := le_sup_left.trans le_sup_right
  have hJH : J ≤ H := sup_le
    (conjugateSpanBy_le hKH ((le_sup_right.trans hH.1.2).trans H.le_normalizer)) hH.1.2
  have hm := (LocalFitting.source_component d hH hsource
    (SolvableSource.solvable_overgroup_source d h hF9all hcentral hcomm hsource)
    K hKH hK).2.1
  have he : (K ⊔ (T : Subgroup G)) ⊔ one L T V₁ = J := by
    apply le_antisymm (sup_le (sup_le hKJ hTJ) hLJ)
    apply sup_le
    · exact conjugateSpanBy_le (le_sup_left.trans le_sup_left)
        ((le_sup_right.trans le_sup_left).trans ((K ⊔ (T : Subgroup G)) ⊔ one L T V₁).le_normalizer)
    · exact sup_le le_sup_right (le_sup_right.trans le_sup_left)
  have hJ : J ∈ Source.Hz (one L T V₁) T G₁ M := he ▸ hm
  exact ⟨hJ, hJH, hKJ, hK.subgroupOf_of_le hKJ hJH⟩

/-- Only an actual Suzuki quotient can remain in the nonnormal source branch. -/
theorem source_normal_or_suzuki :
    (K.subgroupOf H).Normal ∨
      ∃ m : ℕ, 1 ≤ m ∧ Nonempty ((K ⧸ pCore 2 K) ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  classical
  by_cases hn : (K.subgroupOf H).Normal
  · exact Or.inl hn
  right
  let J := conjugateSpanBy K (T : Subgroup G) ⊔ (one L T V₁ ⊔ (T : Subgroup G))
  obtain ⟨hJ,hJH,hKJ,hK'⟩ := source_generated_overgroup
    d h hF9all hcentral hcomm hsource hH hKH hK
  have hmove : conjugateSpanBy K (T : Subgroup G) ≠ K := by
    intro he
    exact hn (Swapped.normal_of_sylow_span_eq H K T hKH (le_sup_right.trans hH.1.2)
      (SolvableSource.source_component_orbit d hF9all
        (SolvableSource.covered_normalizer_source d h) hcentral hcomm hsource hH K hK) he)
  have hnJ : ¬ (K.subgroupOf J).Normal := by
    intro hnJ
    exact hmove (conjugateSpan_eq_of_normal J K T hKJ (le_sup_right.trans hJ.1.2) hnJ)
  have models := SourceModels.source_nonnormal_quotient_f918Models
    d h hF9all hcentral hcomm hsource hJ hKJ hK' rfl hnJ
  rcases models with ⟨n,hn,hm⟩ | hs | hm
  · exact (Swapped.LinearTwo.Original.false_of_source d h hF9all hcentral hcomm hsource
      hJ hKJ hK' hn (hm.of_mulEquiv (componentStarEquiv J K hKJ hK').symm) rfl hmove).elim
  · exact hs
  · exact (Swapped.LinearThree.Original.false_of_source d h hF9all hcentral hcomm hsource
      hJ hKJ hK' (hm.of_mulEquiv (componentStarEquiv J K hKJ hK').symm) rfl hmove).elim

/-- The concrete source catalogue before the remaining Suzuki exclusion. -/
theorem source_catalogue_or_suzuki : Models.ComponentModelOrSuzuki (Source.starImage H K) := by
  rcases source_normal_or_suzuki d h hF9all hcentral hcomm hsource hH hKH hK with hn | ⟨m,hm,⟨e⟩⟩
  · let J := conjugateSpanBy K (T : Subgroup G) ⊔ (one L T V₁ ⊔ (T : Subgroup G))
    obtain ⟨hJ,hJH,hKJ,hK'⟩ := source_generated_overgroup
      d h hF9all hcentral hcomm hsource hH hKH hK
    let := hn
    have hnJ : (K.subgroupOf J).Normal :=
      (normal_subgroupOf_iff_le_normalizer hKJ).mpr
        (hJH.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hn))
    have hc := SourceModels.source_normal_catalogue_or_suzuki
      d h hF9all hcentral hcomm hsource hJ hKJ hK' rfl hnJ
    let e := (componentStarEquiv H K hKH hK).symm.trans (componentStarEquiv J K hKJ hK')
    rcases hc with hc | ⟨m,hm,⟨f⟩⟩
    · exact Or.inl (hc.of_mulEquiv e)
    · exact Or.inr ⟨m,hm,⟨e.trans f⟩⟩
  · exact Or.inr ⟨m,hm,⟨(componentStarEquiv H K hKH hK).symm.trans e⟩⟩

omit hsource in
/-- The original normality reduction with the completed 13.3.9 producer applied. -/
theorem original_normal_or_suzuki :
    (K.subgroupOf H).Normal ∨
      ∃ m : ℕ, 1 ≤ m ∧ Nonempty ((K ⧸ pCore 2 K) ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :=
  source_normal_or_suzuki d h hF9all hcentral hcomm
    (EarlierResidual.original_source d h) hH hKH hK

omit hsource in
/-- The original concrete catalogue reduction, with no 13.3.9 callback. -/
theorem original_catalogue_or_suzuki : Models.ComponentModelOrSuzuki (Source.starImage H K) :=
  source_catalogue_or_suzuki d h hF9all hcentral hcomm
    (EarlierResidual.original_source d h) hH hKH hK

end CFSG.Quasithin.Chapter13.Section08.Components
