module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.ComponentSelection
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration.Source.Module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration.Source.Pairs

/-!
# The marked configuration for the original selected A₅ component

The source selection is connected to the existing prefix theorem on the
literal X/C_X(K*) quotient. The actual F.9 quotient action also satisfies
condition (iii), with its original moved seed, and condition (iv), by transport
of the genuine F.9.5(6) pair theorem. The O₂,₃ containment is a separate source clause.
Source: Aschbacher–Smith13.5.21, printed pp.923–924.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
open ComponentReduction Recognition Recognition.Configuration
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

/-- Original condition(iii), with no extra module or moved-space premise. -/
theorem source_component_module_conditions :
    let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
    let hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
    ModuleConditions D hf := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  apply source_module_conditions hf d.third_index hU d.module_card
  change V₃ = ⁅V₃,residualCentralizer L V₁⁆
  conv_rhs => rw [d.third_eq_commutator]
  rw [commutator_isPPerfect_idempotent (residualCentralizer L V₁) V
    (isPPerfect_embedded_pResidual 2 _) (IsElementaryAbelian.isPGroup 2 V)
    ((map_subtype_le _).trans (inf_le_left.trans d.chosen.normalizes))]
  exact d.third_eq_commutator

variable
  (h17 : ∀ J ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)),
    ¬ IsMulCommutative (Source.UH J V₃) → ((residualCentralizer L V₁).subgroupOf J).Normal →
      ClassicalGroup.IsPSU G 4 2 ∨ ClassicalGroup.IsPSL G 4 3)
  (hnot : ¬ ModelConclusion G 5)
include h17 hnot

/-- The original moved component, its literal marked prefix and module clause. -/
theorem source_component_configuration_prefix :
    let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
    let hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
    ∃ K : Subgroup G, ∃ s : Selected D K,
      let := componentCentralizer_normal s hf
        (selected_star_local_normalization s hf d.hypothesis.qtke hH.1.1)
      Prefix s hf D.L₁ ∧ ModuleConditions D hf ∧ PairCondition s hf := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  obtain ⟨K,hKH,hK,hq,he,hm⟩ := source_component_selection d hA312 hH hU h17 hnot
  let s : Selected D K := ⟨hKH,hK,hq,he,hm⟩
  obtain ⟨himage,hcore⟩ := source13_5_19 d hA312 hH h17 hnot
  let := componentCentralizer_normal s hf
    (selected_star_local_normalization s hf d.hypothesis.qtke hH.1.1)
  have hp : ∀ x : Source.Hstar D.H, ¬ IsPGroup 2
      (Source.starImage D.H D.V ⊔ (Source.starImage D.H D.V).map (MulAut.conj x).toMonoidHom : Subgroup _) →
      Nonempty ((Source.starImage D.H D.V ⊔ (Source.starImage D.H D.V).map (MulAut.conj x).toMonoidHom : Subgroup _) ≃* Equiv.Perm (Fin 3)) :=
    (source_component_action_complete d hA312 hH hU).2.2
  exact ⟨K,s,source_prefix s hf d.hypothesis.qtke hH.1.1 d.third_index hU D.L₁ le_rfl
    himage hcore,source_component_module_conditions d hA312 hH hU,
    source_pair_condition s hf
      ((le_inf hf.V_le_T (selected_actor_normalization s hf d.third_index hU).1).trans
        (le_sup_right.trans le_sup_right)) hp⟩
end CFSG.Quasithin.Chapter13.Section05.A5Source
