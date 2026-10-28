module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.ChiefActions
public import CFSG.Quasithin.Chapter13.Section05.A5Source.CentralCoverNormalizer
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration.Source.LocalCore
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.ChiefComparison

/-!
# The complete original A₅ configuration before B.4

Original13.5.18–20 selects the moved component. The genuine F.9.5 source
identities and coprime central-cover lifting supply all four marked clauses
on the literal quotient X/C_X(K*). The same selected component has the full
B.4 hypotheses on every noncentral irreducible chief action image.

The only earlier source premises are full A.3.12 and the original normal
branch13.5.17, together with the contradiction assumption excluding its two
conclusions. The subsequent complete B.4 catalogue and model elimination
are separate from this constructed configuration.
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

/-- Every marked clause of the original pre-B.4 configuration is constructed. -/
theorem source_component_configuration :
    let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
    let hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
    ∃ K : Subgroup G, ∃ s : Selected D K,
      let := componentCentralizer_normal s hf
        (selected_star_local_normalization s hf d.hypothesis.qtke hH.1.1)
      SourceConfiguration s hf D.L₁ le_rfl := by
  intro D hf
  obtain ⟨K,s,p,hm,hpair⟩ := source_component_configuration_prefix d hA312 hH hU h17 hnot
  let := componentCentralizer_normal s hf
    (selected_star_local_normalization s hf d.hypothesis.qtke hH.1.1)
  have hv : D.V ≤ X D K :=
    (le_inf hf.V_le_T (selected_actor_normalization s hf d.third_index hU).1).trans
      (le_sup_right.trans le_sup_right)
  have hk := source_Khat_actor_centralizer_normalizes_local d hA312 hH hU K s
  have hc : Nat.card (D.L₁ ⧸ pCore 2 D.L₁) = 3 := residual_quotient_card d hA312 hH hU
  exact ⟨K,s,SourceConfiguration.of_prefix s hf D.L₁ le_rfl p
    (source_local_core_condition s hf D.L₁ p d.third_index hU hv hc hk) hm hpair⟩

/-- Configuration and chief-action hypotheses use the same original selected component. -/
theorem source_component_preclassification :
    let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
    let hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
    let := Action.point_normal D hf
    let := Action.quotient_elementary D hf
    ∃ K : Subgroup G, ∃ s : Selected D K,
      let := componentCentralizer_normal s hf
        (selected_star_local_normalization s hf d.hypothesis.qtke hH.1.1)
      SourceConfiguration s hf D.L₁ le_rfl ∧ ChiefHypotheses D K hf := by
  intro D hf
  let := Action.point_normal D hf
  let := Action.quotient_elementary D hf
  obtain ⟨K,s,hc⟩ := source_component_configuration d hA312 hH hU h17 hnot
  let := componentCentralizer_normal s hf
    (selected_star_local_normalization s hf d.hypothesis.qtke hH.1.1)
  exact ⟨K,s,hc,source_chief_hypotheses_all D K hf s d.hypothesis.qtke hH.1.1
    d.third_index hU d.module_card⟩
end CFSG.Quasithin.Chapter13.Section05.A5Source
