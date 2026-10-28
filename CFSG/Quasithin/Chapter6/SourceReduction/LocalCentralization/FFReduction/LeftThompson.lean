module
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FFReduction.OmegaAction
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FFReduction.BaumannControl
public import CFSG.Quasithin.Chapter3.Section01.Source318Movement
public import CFSG.Quasithin.Chapter3.Section02.QrcInput
/-!
# The original rank-one Thompson equality

The initial rank-one input supplies the literal qrc hypotheses on L∨T,
including the centralizer of its original W. Source 3.1.8(3) turns movement
of the Sylow omega-center by the original comparison group into Thompson
movement. The quasisimple core commutator argument then gives L=[L,J(T)].
Source: Aschbacher--Smith 5.1.13 p.637 and 3.1.8(3) p.576.
-/
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H : Subgroup G} {n : ℕ}
namespace Input

/-- The original chosen reduced module supplies source Hypothesis 3.1.5. -/
theorem qrc_hypotheses (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    Chapter3.QrcHypotheses T (normalizer (L : Set G)) (L ⊔ (T : Subgroup G)) H W := by
  refine ⟨le_sup_right,sup_le L.le_normalizer h.sylow_normalizes,hH,h.reduced.1,
    reduced_normalizes h.reduced,h.reduced.2.1,?_,h.sylow_centralizer_eq_core.symm,Or.inl ?_⟩
  · exact Chapter3.Section02.internalActionImage_core_of_reduced _ _ h.reduced.1
      (reduced_normalizes h.reduced) h.reduced_internal
  · rw [embedded_pResidual_join_pGroup L (T : Subgroup G) h.local_mem.2.2.1
      T.isPGroup' h.sylow_normalizes]
    exact inf_le_right

/-- Noncentrality of the original omega-center forces actual Thompson movement. -/
theorem thompson_moves_of_noncentral_omega (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype) :
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G) := by
  apply (h.qrc_hypotheses hH).thompson_moves_of_noncentral_omega
    h.qtke h.maximal h.unique_local_join ?_ hZ
  intro he
  exact h.noncentral (by rw [he,commutator_bot_left])

/-- The original local rank-one component is its full Thompson commutator. -/
theorem thompson_commutator_of_noncentral_omega
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype) :
    ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆ = L := by
  let M := L ⊔ (T : Subgroup G)
  let B := L.subgroupOf M
  let U := W.subgroupOf M
  let S := T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)
  let J := elementaryAbelianMaxJ (S : Subgroup M)
  have hr : IsPReduced 2 U := h.reduced_internal
  let := hr.normal
  let : B.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer h.sylow_normalizes)
  have hB : B.IsCComponent := h.maximal_local.1.1
  let := h.quotient_quasisimple
  let e := QuotientGroup.congr (pCore 2 B) (pCore 2 L)
    (subgroupOfEquivOfLe (show L ≤ M from le_sup_left))
    (pCore_map_iso 2 (subgroupOfEquivOfLe (show L ≤ M from le_sup_left)))
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv e.symm
  have hgen : B ⊔ (S : Subgroup M) = ⊤ := by
    change L.subgroupOf M ⊔ (T : Subgroup G).subgroupOf M = ⊤
    rw [←subgroupOf_sup (show L ≤ M from le_sup_left) le_sup_right,subgroupOf_self]
  have hjmap : J.map M.subtype = elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective M.subtype M.subtype_injective]
    congr 1
    exact map_subgroupOf_eq_of_le le_sup_right
  have hj : ¬ J ≤ centralizer (U : Set M) := by
    intro hc
    apply h.thompson_moves_of_noncentral_omega hH hZ
    rw [←hjmap]
    rintro _ ⟨x,hx,rfl⟩ y hy
    exact congrArg M.subtype (hc hx ⟨y,h.reduced.1 hy⟩ hy)
  have hnot : ¬ B ≤ normalizer (J : Set M) := by
    intro hb
    let : J.Normal := normalizer_eq_top_iff.mp (top_unique (by
      rw [←hgen]
      exact sup_le hb ((S : Subgroup M).le_normalizer.trans
        (normalizer_le_normalizer_elementaryAbelianMaxJ _))))
    have hp : IsPGroup 2 J := S.isPGroup'.to_le (sSup_le fun _ hA => hA.1)
    exact hj ((show J ≤ pCore 2 M from le_sSup ⟨inferInstance,hp⟩).trans
      (le_centralizer_iff.mp hr.le_centralizer_pCore))
  have hh := congrArg (map M.subtype)
    (eq_commutator_maxJ_of_quasisimple_core_of_not_normalizes S B hB hgen hnot)
  rw [map_commutator,hjmap,map_subgroupOf_eq_of_le (show L ≤ M from le_sup_left)] at hh
  exact hh.symm
end Input
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
