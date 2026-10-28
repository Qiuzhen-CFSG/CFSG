module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.FullConfiguration
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.BinaryComponentGroups

/-!
# The selected component in the original A₅ source

The actual source configuration supplies the complete binary component
catalogue. Its center and outer-group calculations show that the same star
component is simple, contains the original cubic residual, and is normal
in H. This removes those three inputs from the subsequent natural-module
recognition. Only the earlier A.3.12 and normal-branch recognition inputs
used by source component selection remain explicit.
Source: Aschbacher--Smith13.5.21(1),(5), printed pp.923--924.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
open ComponentReduction Recognition Recognition.Configuration Recognition.Catalogue
open Representation Representation.BinaryOffender
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
  (hU : ¬ IsMulCommutative (Source.UH H V₃))
include d hA312 hH hU

variable
  (h17 : ∀ J ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)),
    ¬ IsMulCommutative (Source.UH J V₃) → ((residualCentralizer L V₁).subgroupOf J).Normal →
      ClassicalGroup.IsPSU G 4 2 ∨ ClassicalGroup.IsPSL G 4 3)
  (hnot : ¬ ModelConclusion G 5)
include h17 hnot

/-- The original selected component is simple and contains the original local
residual; its normality is proved in the same ambient H. -/
theorem source_exists_simple_component :
    let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
    let hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
    ∃ K : Subgroup G, ∃ s : Selected D K,
      let := componentCentralizer_normal s hf
        (selected_star_local_normalization s hf d.hypothesis.qtke hH.1.1)
      SourceConfiguration s hf D.L₁ le_rfl ∧ center (Source.starImage H K) = ⊥ ∧
        IsSimpleGroup (Source.starImage H K) ∧
          residualCentralizer L V₁ ≤ K ∧ (K.subgroupOf H).Normal := by
  intro D hf
  let := Action.point_normal D hf
  let := Action.quotient_elementary D hf
  obtain ⟨K,s,c⟩ := source_component_configuration d hA312 hH hU h17 hnot
  let := componentCentralizer_normal s hf
    (selected_star_local_normalization s hf d.hypothesis.qtke hH.1.1)
  exact ⟨K,s,c,
    Catalogue.source_component_center_eq_bot D K hf s d.hypothesis.qtke hH.1.1
      d.third_index hU d.module_card c,
    Catalogue.source_component_simple D K hf s d.hypothesis.qtke hH.1.1
      d.third_index hU d.module_card c,
    Catalogue.source_local_le_component D K hf s d.hypothesis.qtke hH.1.1
      d.third_index hU d.module_card c (residual_quotient_card d hA312 hH hU)⟩

end CFSG.Quasithin.Chapter13.Section05.A5Source
