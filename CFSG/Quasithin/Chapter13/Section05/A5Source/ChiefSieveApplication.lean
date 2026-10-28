module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.MarkedChiefActions
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.ChiefSieve

/-!
# The complete catalogue and proved row exclusions in the original A₅ branch

One actual selected component retains the full source configuration and the
complete B.4 catalogue on every noncentral irreducible chief section. Seven
source exclusions are now attached to those same literal chief actions.
Only the original earlier A.3.12 and normal-branch13.5.17 inputs remain
explicit at this pre-elimination boundary.
Source: Aschbacher–Smith13.5.21, pp.923–924.
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

/-- The original context supplies the full chief catalogue with all seven proved source exclusions. -/
theorem source_component_chief_sieve :
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
          ChiefSieve (imageRepresentation (chiefRepresentation D K hf U N)) := by
  intro D hf
  let := Action.point_normal D hf
  let := Action.quotient_elementary D hf
  obtain ⟨K,s,hc,_,_⟩ := source_component_preclassification_marked d hA312 hH hU h17 hnot
  let := componentCentralizer_normal s hf
    (selected_star_local_normalization s hf d.hypothesis.qtke hH.1.1)
  refine ⟨K,s,hc,?_⟩
  intro U N hn hirr
  exact source_chief_sieve D K hf s d.hypothesis.qtke hH.1.1
    d.third_index hU d.module_card U N hn hirr D.L₁ le_rfl hc
end CFSG.Quasithin.Chapter13.Section05.A5Source
