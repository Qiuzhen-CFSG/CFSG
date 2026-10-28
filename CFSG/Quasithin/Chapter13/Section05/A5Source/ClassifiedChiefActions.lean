module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.MarkedChiefActions
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.MarkedSourceCatalogue

/-!
# The complete chief-action catalogue on the original A₅ source context

The existing selection and marked-chief theorems construct one actual
component and the four original local configuration clauses. The complete
marked source classifier now determines every noncentral irreducible chief
action of that same component. This discharges the B.4.2/B.4.5 catalogue
input in 13.5.21 without a classifier or narrowed model-list premise.

The independent earlier A.3.12 and normal-branch 13.5.17 assumptions are
retained exactly as in the existing source context; their discharge remains
with the chapter assembly.
Source: Aschbacher–Smith 13.5.21, printed pp.923–924.
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

/-- The original source context supplies the full catalogue for its actual chief actions. -/
theorem source_component_fullCatalogue :
    let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
    let hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
    let := Action.point_normal D hf
    let := Action.quotient_elementary D hf
    ∃ K : Subgroup G, ∃ s : Selected D K,
      let := componentCentralizer_normal s hf
        (selected_star_local_normalization s hf d.hypothesis.qtke hH.1.1)
      SourceConfiguration s hf D.L₁ le_rfl ∧
        ∀ U N : Subrepresentation (representation D K hf),
          ¬ component D K ≤ (chiefRepresentation D K hf U N).ker →
          IsIrreducible (chiefRepresentation D K hf U N) →
          FullCatalogueAction (imageRepresentation (chiefRepresentation D K hf U N)) := by
  intro D hf
  let := Action.point_normal D hf
  let := Action.quotient_elementary D hf
  obtain ⟨K,s,hc,_,_⟩ := source_component_preclassification_marked d hA312 hH hU h17 hnot
  let := componentCentralizer_normal s hf
    (selected_star_local_normalization s hf d.hypothesis.qtke hH.1.1)
  refine ⟨K,s,hc,?_⟩
  intro U N hn hirr
  exact source_chief_fullCatalogue D K hf s d.hypothesis.qtke hH.1.1
    d.third_index hU d.module_card U N hn hirr
end CFSG.Quasithin.Chapter13.Section05.A5Source
