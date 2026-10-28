module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.BinaryComponentGroups
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.Configuration

/-!
# The selected component in the original ordinary-A₆ source

Apply the source configuration and complete binary component catalogue to
its actual K* inside H/O₂(H). The natural flag supplies |V|=16 and the original
cubic quotient of L₁. Thus K* is centerless and simple, L₁ lies in K, and K is
normal in H, with no model or chief-classification premise.

Source: Aschbacher–Smith13.5.21(1), printed p.924.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix
open Subgroup Theory.GroupTheory
open Section08.SourceCompletion Section08.Source Recognition
open CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz) (h : D.Hypothesis)
  (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
include d h e

/-- The original ordinary-A₆ configuration has a simple selected star component,
and the original local residual lies in the same selected component. -/
theorem source_component_structure (hU : ¬ IsMulCommutative D.UH)
    (K : Subgroup G) (s : Selected D K) [(componentCentralizer s h).Normal]
    (c : SourceConfiguration s h D.L₁ le_rfl) :
    center (starImage D.H K) = ⊥ ∧ IsSimpleGroup (starImage D.H K) ∧
      D.L₁ ≤ K ∧ (K.subgroupOf D.H).Normal := by
  have hi := NormalBranch.SourceOrthogonal.seed_index d
  have hc := NormalBranch.ReturningPlane.module_card d
  exact ⟨Catalogue.source_component_center_eq_bot D K h s d.counterexample.qtke
      (selected_H_mem h) hi hU hc c,
    Catalogue.source_component_simple D K h s d.counterexample.qtke
      (selected_H_mem h) hi hU hc c,
    Catalogue.source_local_le_component D K h s d.counterexample.qtke
      (selected_H_mem h) hi hU hc c
      (NormalBranch.SourceStar.original_residual_quotient_card d h e)⟩

/-- Apply the actual source selector and discharge its group conclusions together. -/
theorem source_exists_simple_component (hU : ¬ IsMulCommutative D.UH)
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L)
    (hc : centralizer (D.Vplus : Set G) ≤ M ⊓ normalizer (D.V : Set G)) :
    ∃ K : Subgroup G, ∃ s : Selected D K,
      let := componentCentralizer_normal s h
        (selected_star_local_normalization s h d.counterexample.qtke (selected_H_mem h))
      SourceConfiguration s h D.L₁ le_rfl ∧ center (starImage D.H K) = ⊥ ∧
        IsSimpleGroup (starImage D.H K) ∧ D.L₁ ≤ K ∧ (K.subgroupOf D.H).Normal := by
  obtain ⟨K,s,c⟩ := exists_source_configuration d h e hU h1221 hc
  let := componentCentralizer_normal s h
    (selected_star_local_normalization s h d.counterexample.qtke (selected_H_mem h))
  exact ⟨K,s,c,source_component_structure d h e hU K s c⟩
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix
