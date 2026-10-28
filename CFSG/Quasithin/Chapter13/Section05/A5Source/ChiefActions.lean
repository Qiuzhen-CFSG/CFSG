module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.ComponentConfiguration
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.SourceChiefImages

/-!
# The original A₅ chief-action inputs to B.4

The genuine selected component and original F.9 quotient action supply a
marked generator of V*. Every noncentral irreducible K*V*-chief section
satisfies the full B.4 hypotheses. The SQTK and irreducibility conditions
are proved on the literal action image, including possible odd central kernels.
Only the earlier full A.3.12 and original normal-branch recognition remain.
Source: Aschbacher–Smith13.5.21, printed pp.923–924.
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

/-- Literal B.4 chief hypotheses for the original selected source component. -/
theorem source_component_chief_actions :
    let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
    let hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
    let := Action.point_normal D hf
    let := Action.quotient_elementary D hf
    ∃ K : Subgroup G, ∃ _s : Selected D K, ChiefHypotheses D K hf := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  let := Action.point_normal D hf
  let := Action.quotient_elementary D hf
  obtain ⟨K,hKH,hK,hq,he,hm⟩ := source_component_selection d hA312 hH hU h17 hnot
  let s : Selected D K := ⟨hKH,hK,hq,he,hm⟩
  exact ⟨K,s,source_chief_hypotheses_all D K hf s d.hypothesis.qtke hH.1.1
    d.third_index hU d.module_card⟩

end CFSG.Quasithin.Chapter13.Section05.A5Source
