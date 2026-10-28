module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration.CentralCoverNormalizer
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration.Source.LocalCore
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration.Source.Module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration.Source.Pairs

/-!
# The ordinary A₆ source configuration for component recognition

The selected component and the source normalizer conclusions supply the
proved pre-B.4 prefix. F.9.5 supplies the actual pair and module conditions.
The genuine maximal-local normalizer bound supplies the remaining
component-centralizer normalization, hence the literal O₂,₃ condition.
All fields retain the original marked quotient and seed action.
Source: Aschbacher–Smith13.5.21, printed p.923.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix
open Section08.SourceCompletion Section08.Source Recognition Recognition.Configuration
open Fitting.SourceAction
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz) (h : D.Hypothesis)
  (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
include h

/-- The actual point gives a nontrivial two-core in the selected H. -/
theorem selected_H_mem : D.H ∈ Chapter1.H G := by
  change D.QH ≠ ⊥
  intro he
  have hp : D.V₁ ≤ D.QH := (h.point_lt.le.trans (le_conjugateSpanBy _ _)).trans h.UH_le_QH
  have hz : D.V₁ = ⊥ := bot_unique (hp.trans_eq he)
  have hc := h.point_card
  rw [hz,card_bot] at hc
  contradiction

include d e
/-- The complete original configuration, with all pre-B.4 source fields
constructed for the very same selected component. -/
theorem exists_source_configuration
    (hU : ¬IsMulCommutative D.UH)
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L)
    (hc : centralizer (D.Vplus : Set G) ≤ M ⊓ normalizer (D.V : Set G)) :
    ∃ K : Subgroup G, ∃ s : Selected D K,
      let := componentCentralizer_normal s h
        (selected_star_local_normalization s h d.counterexample.qtke (selected_H_mem h))
      SourceConfiguration s h D.L₁ le_rfl := by
  obtain ⟨K,hKH,hK,hqs,hq,hm⟩ := exists_component d h e hU h1221 hc
  let s : Selected D K := ⟨hKH,hK,hqs,hq,hm⟩
  let := componentCentralizer_normal s h
    (selected_star_local_normalization s h d.counterexample.qtke (selected_H_mem h))
  have hi := NormalBranch.SourceOrthogonal.seed_index d
  obtain ⟨himage,hcore⟩ := normalizer_conclusions d h e h1221 hc
  have p := source_prefix s h d.counterexample.qtke (selected_H_mem h)
    hi hU D.L₁ le_rfl himage hcore
  have hv : D.V ≤ X D K :=
    (le_inf h.V_le_T (selected_actor_normalization s h hi hU).1).trans
      (le_sup_right.trans le_sup_right)
  have hNL := h1221.normal_subgroup_normalizer_le d.normalizes_L
    h.V_le_LT d.chosen.ne_bot d.normalizes_V
  have hk := Khat_actor_centralizer_normalizes_local s h hi hU (inf_le_right.trans hNL)
  have hl : D.Vplus = ⁅D.Vplus,D.L₁⁆ := by
    rw [residual_eq_sourceOne d h]
    exact (Section07.ModelExclusions.seed_commutator_point_residual d).symm
  have hmodule := source_module_conditions h hi hU (NormalBranch.ReturningPlane.module_card d) hl
  have hcentral : ⁅D.V,D.H ⊓ centralizer (D.Vplus : Set G)⁆ ≤ D.V₁ :=
    (commutator_mono le_rfl inf_le_right).trans
      (AmbientSource.source_seed_centralizer_displacement d hc)
  have hpairs : ∀ x : Hstar D.H,
      ¬IsPGroup 2 (starImage D.H D.V ⊔ (starImage D.H D.V).conjBy x : Subgroup _) →
      Nonempty ((starImage D.H D.V ⊔ (starImage D.H D.V).conjBy x : Subgroup _) ≃*
        Equiv.Perm (Fin 3)) := by
    intro x hx
    obtain ⟨g,hg,_,he⟩ := lift_pair D.H D.V h.V_le_H x
    have hne : starImage D.H D.V ≠ ⊥ := by
      intro hz
      have hh := LocalGeometry.star_V_card_two h hi hU
      rw [hz,card_bot] at hh
      contradiction
    have hs := source_F95Six D h hi hne
      (fun g hg hI => twoGroup_pairs d h hU (D.H.inv_mem hg) hI)
      hcentral (NormalBranch.ReturningPlane.module_card d) g hg (he.symm ▸ hx)
    exact he ▸ hs
  exact ⟨K,s,SourceConfiguration.of_prefix s h D.L₁ le_rfl p
    (source_local_core_condition s h D.L₁ p hi hU hv
      (NormalBranch.SourceStar.original_residual_quotient_card d h e) hk)
    hmodule (source_pair_condition s h hv hpairs)⟩
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix
