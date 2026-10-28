module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedReduction
public import CFSG.Quasithin.ChapterE.Section06.Basic
public import CFSG.Quasithin.ChapterE.Section03.Parameters
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.WeakClosure.Generation
public import CFSG.Quasithin.Chapter3.Section01.StandingGuard

/-!
# E.6.1 and the weak-closure deductions for the natural layer

Irreducibility of the marked natural module makes its M-conjugates equal
or disjoint. The local action kernel is O₂(LT), which is also the Sylow
centralizer of the layer. Thus uniqueness over LT supplies the exact
uniqueness subgroup of E.6.1.

For generation-one H-star members, the proved E.3.19 identity gives the
normalizer/centralizer escape disjunction as soon as s(G,B) > 1. E.3.10
puts every conjugate-corank generator with n-i ≥ 2 into the A₂ fixed-space
family or makes it centralize B. Consequently the natural-module A₂
control gives W₀ ≤ C_T(Z_S) and, for n > 2, Z_S ≤ C₁.

The rank equality and the A₂ control are explicit earlier-source inputs;
this module does not assert their unconditional natural-module proofs.
Source: Aschbacher--Smith, 6.1.7(2), 6.1.10 and 6.1.12, pp.669--670;
E.3.10 and E.3.19, pp.232--235.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
  {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}


/-- Source 6.1.7(1): the natural layer is TI under the relative normalizer M. -/
theorem natural_layer_ti (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n) {g : G} (hg : g ∈ M) :
    layer L V ⊓ (layer L V).map (MulAut.conj g).toMonoidHom = ⊥ ∨
      (layer L V).map (MulAut.conj g).toMonoidHom = layer L V := by
  have hnL : L ≤ normalizer (layer L V : Set G) := by
    obtain ⟨F, _, _, _, _, hmodel⟩ := hnatural
    exact hmodel.normalizes
  have hgL : L.map (MulAut.conj g).toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp
      (((normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal) hg)
  have hnLg : L ≤ normalizer ((layer L V).map (MulAut.conj g).toMonoidHom : Set G) := by
    have hm := map_mono (f := (MulAut.conj g).toMonoidHom) hnL
    rwa [hgL, map_equiv_normalizer_eq] at hm
  rcases hnatural.invariant_subgroup
      (layer L V ⊓ (layer L V).map (MulAut.conj g).toMonoidHom)
      inf_le_left ((le_inf hnL hnLg).trans inf_normalizer_le_normalizer_inf) with he | he
  · exact Or.inl he
  · right
    symm
    apply eq_of_le_of_card_ge (he.symm.le.trans inf_le_right)
    rw [card_map_of_injective (MulAut.conj g).injective]

/-- The Sylow centralizer is the literal two-core of LT. -/
theorem sylow_layer_centralizer_eq_core (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n) :
    ChapterE.Section06.sylowCentralizer (T : Subgroup G) (layer L V) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hQ : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    obtain ⟨S, hS⟩ := h.local_mem.1.prop.2.1
    exact (pCoreIn_le_sylow _ S).trans_eq hS
  apply le_antisymm
  · exact (inf_le_inf_right _ le_sup_right).trans_eq
      (local_layer_centralizer_eq_core h hnatural)
  · exact le_inf hQ (local_core_centralizes_layer h)

/-- E.6.1 applies to the original natural layer. -/
theorem natural_layer_hypothesisE61 (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ⊔ (T : Subgroup G) ≤ N → N = M) :
    ChapterE.Section06.HypothesisE61 κ T M (layer L V) := by
  have hnL : L ≤ normalizer (layer L V : Set G) := by
    obtain ⟨F, _, _, _, _, hmodel⟩ := hnatural
    exact hmodel.normalizes
  have hHN : L ⊔ (T : Subgroup G) ≤ normalizer (layer L V : Set G) :=
    sup_le hnL h.sylow_normalizes_layer
  refine ⟨h.simpleQTKE, h.maximal, h.sylow_le, h.nontrivial_action,
    h.layer_elementary, h.layer_le_T,
    (normal_subgroupOf_iff_le_normalizer h.layer_le_T).mpr h.sylow_normalizes_layer,
    fun g hg => natural_layer_ti h hnatural hg, ?_⟩
  intro N hN hle
  apply hunique N hN
  apply le_trans ?_ hle
  refine le_inf (le_inf (sup_le h.L_le h.sylow_le) hHN) ?_
  rw [sylow_layer_centralizer_eq_core h hnatural]
  exact (L ⊔ (T : Subgroup G)).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))


/-- E.3.19 and generation one give the escape alternative of 6.1.12(1). -/
theorem weak_closure_escape_of_one_lt_globalS (h : Hypothesis611 κ T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hs : letI := h.layer_elementary; (1 : ℕ∞) < ChapterE.globalS (layer L V)) :
    ¬ normalizer (W (layer L V) (T : Subgroup G) 0 : Set G) ≤ M ∨
      ¬ centralizer (C (layer L V) (T : Subgroup G) 1 : Set G) ≤ M := by
  classical
  let := h.layer_elementary
  by_contra! hbounds
  obtain ⟨H, hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside hout
  have hT : ((T.subtype hH.1.1.2 : Sylow 2 H) : Subgroup H).map H.subtype =
      (T : Subgroup G) := map_subgroupOf_eq_of_le hH.1.1.2
  apply hH.1.2
  apply ChapterE.RankOneWeakClosure.le_of_parameter_eq_one
    (V := layer L V) (T.subtype hH.1.1.2) (h.generation_one H hH) hs
  · rw [hT]
    exact hbounds.2
  · rw [hT]
    exact hbounds.1

/-- E.3.10 puts every small-corank generator into the controlled A₂ family. -/
theorem W_le_line_centralizer_of_fixedSpace_control
    (h : Hypothesis611 κ T L M V n)
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L V) = n)
    (hcontrol : letI := h.layer_elementary;
      ∀ A : Subgroup G, A ≤ (T : Subgroup G) →
        ChapterE.inducedAutomizer (layer L V) A ∈
          ChapterE.fixedSpaceFamily (ChapterE.automizerRepresentation (layer L V)) 2 →
        A ≤ centralizer (ZS (T : Subgroup G) L V : Set G))
    {i : ℕ} (hi : i + 2 ≤ n) :
    W (layer L V) (T : Subgroup G) i ≤
      (T : Subgroup G) ⊓ centralizer (ZS (T : Subgroup G) L V : Set G) := by
  let := h.layer_elementary
  apply le_inf (W_le _ _ _) ?_
  change sSup (ChapterE.gamma (layer L V) (T : Subgroup G) i) ≤ _
  apply sSup_le
  rintro A ⟨⟨g, hAg, hidx⟩, hAT⟩
  by_cases hc : (layer L V).map (MulAut.conj g).toMonoidHom ≤
      centralizer (layer L V : Set G)
  · exact (hAg.trans hc).trans (centralizer_le inf_le_left)
  have hcomm : ⁅layer L V, (layer L V).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ := by
    intro he
    exact hc (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he))
  have hcor : ChapterE.subgroupCorank
      ((layer L V).map (MulAut.conj g).toMonoidHom) A = i := by
    simp only [ChapterE.subgroupCorank, hidx, Nat.log_pow Nat.one_lt_two]
  have hsmall : (ChapterE.subgroupCorank
      ((layer L V).map (MulAut.conj g).toMonoidHom) A : ℕ∞) <
      ChapterE.globalS (layer L V) := by
    rw [hcor, hs]
    exact ENat.natCast_lt_natCast.mpr (by omega)
  have hf := (ChapterE.inducedAutomizer_mem_fixedSpaceFamily_of_corank_lt_globalS
    g (le_inf hAg (hAT.trans h.sylow_normalizes_layer)) hsmall hcomm).2
  rw [hs, ENat.toNat_natCast, hcor] at hf
  exact hcontrol A hAT (ChapterE.fixedSpaceFamily_mono _ (by decide) (by omega) hf)

/-- The same A₂ control supplies precisely the two containments of 6.1.12. -/
theorem weak_closure_bounds_of_fixedSpace_control
    (h : Hypothesis611 κ T L M V n)
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L V) = n)
    (hcontrol : letI := h.layer_elementary;
      ∀ A : Subgroup G, A ≤ (T : Subgroup G) →
        ChapterE.inducedAutomizer (layer L V) A ∈
          ChapterE.fixedSpaceFamily (ChapterE.automizerRepresentation (layer L V)) 2 →
        A ≤ centralizer (ZS (T : Subgroup G) L V : Set G)) :
    (2 < n → ZS (T : Subgroup G) L V ≤ C (layer L V) (T : Subgroup G) 1) ∧
      W (layer L V) (T : Subgroup G) 0 ≤
        (T : Subgroup G) ⊓ centralizer (ZS (T : Subgroup G) L V : Set G) := by
  constructor
  · intro hn
    exact (le_C_iff h.ZS_le_T 1).mpr
      (W_le_line_centralizer_of_fixedSpace_control h hs hcontrol (by omega))
  · exact W_le_line_centralizer_of_fixedSpace_control h hs hcontrol (by have := h.n_gt_one; omega)
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
