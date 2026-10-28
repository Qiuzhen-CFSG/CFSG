module
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonMovement
public import Theory.GroupTheory.TwoLocalUniquenessControl

/-!
# Normalizers of the first Thompson fixed subgroup

For the actual chosen elementary subgroup V, retain V_E=C_V(J₁(T)).
Thompson heredity places V_E in Ω₁Z(J₁(T)), so the local residual
centralizers from15.1.12(4) restrict to this same subgroup.

The normalizer conclusions of15.1.14 then use its global residual statement
(1). The Sylow supplement makes C_G(Z) normalize V_E; its unique maximal
two-local overgroup controls N_G(V_E). Heredity also identifies J(J₁(T))
with J(T), placing N_G(J₁(T)) in the selected maximal local and its partner.
The genuine earlier global residual implication is retained explicitly,
without replacing it by local centralization or replacing the chosen V by V(M).

Source: Aschbacher--Smith15.1.14(2--3), printed p.1091, using15.1.14(1),
15.1.9(1), B.2.3(1--3), and the chosen seed from15.1.5(1).
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The subgroup denoted V_E in the source; the chosen V is retained. -/
abbrev thompsonFixed (T : Sylow 2 G) (V : Subgroup G) : Subgroup G :=
  V ⊓ centralizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G)

private theorem normalizer_thompsonJ_le_normalizer_maxJ
    (T : Sylow 2 G) (hr : 1 < ChapterB.twoRank (T : Subgroup G)) :
    normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤
      normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  have hJJ : elementaryAbelianMaxJ (T : Subgroup G) ≤
      ChapterB.thompsonJ (T : Subgroup G) 1 := by
    rw [←ChapterB.thompsonJ_zero]
    exact ChapterB.lemma_B_2_3_1 _ (by omega : 0 ≤ 1) hr
  have he := ChapterB.lemma_B_2_3_3 (T : Subgroup G)
    (ChapterB.thompsonJ (T : Subgroup G) 1) (by omega : 0 < ChapterB.twoRank (T : Subgroup G))
    (show ChapterB.thompsonJ (T : Subgroup G) 0 ≤ ChapterB.thompsonJ (T : Subgroup G) 1 by
      simpa only [ChapterB.thompsonJ_zero] using hJJ)
    (ChapterB.thompsonJ_le _ _)
  rw [ChapterB.thompsonJ_zero,ChapterB.thompsonJ_zero] at he
  rw [he]
  exact normalizer_le_normalizer_elementaryAbelianMaxJ _

private theorem thompsonFixed_nontrivial (T : Sylow 2 G) {M V : Subgroup G}
    (hV : V ≠ ⊥) (hspan : V = conjugateSpanBy (centralInvolutions T ⊓ V) M) :
    thompsonFixed T V ≠ ⊥ := by
  have hseed : centralInvolutions T ⊓ V ≤ thompsonFixed T V := by
    refine le_inf inf_le_right ?_
    intro z hz j hj
    exact ((mem_omegaOneCenterAmbient_iff _ z).mp hz.1).2.2 j
      (ChapterB.thompsonJ_le _ _ hj)
  intro he
  have hz : centralInvolutions T ⊓ V = ⊥ := bot_unique (hseed.trans he.le)
  apply hV
  rw [hspan,hz]
  exact bot_unique (conjugateSpanBy_le bot_le (by
    change M ≤ normalizer (⊥ : Subgroup G)
    rw [normalizer_eq_top]
    exact le_top))

/-- The original chosen fixed subgroup lies in the first Thompson omega-center. -/
theorem PreparedChosenModule.thompsonFixed_le_omega
    (T : Sylow 2 G) {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (h : PreparedChosenModule T M V) :
    thompsonFixed T V ≤ omegaOneCenterAmbient (ChapterB.thompsonJ (T : Subgroup G) 1) := by
  let := h.elementary
  have hr := chosen_twoRank_gt_one_of_quadraticRatio_two T hM.1.2 h.le_selected
    h.normalized h.quadratic_ratio
  let : (V.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer h.normalized
  let := IsElementaryAbelian.subgroupOf h.le_selected (p := 2)
  have hh := (IsElementaryAbelian.isPGroup 2 (V.subgroupOf M)).le_sylow_of_normal
    (T.subtype hM.1.2)
  have hVT : V ≤ (T : Subgroup G) := by
    simpa only [map_subgroupOf_eq_of_le h.le_selected, Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hM.1.2] using map_mono (f := M.subtype) hh
  have hW : thompsonFixed T V ≤ (T : Subgroup G) ⊓
      centralizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) :=
    inf_le_inf_right _ hVT
  rw [←(ChapterB.lemma_B_2_3_2 (T : Subgroup G) (le_refl 1) hr).2]
  intro x hx
  exact (omegaOneAmbient_le_iff _ _).mp le_rfl x (hW hx)
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx.1)

/-- The local source15.1.12(4) centralizers restrict to the actual V_E. -/
theorem PreparedChosenModule.thompsonFixed_local_residuals
    (T : Sylow 2 G) {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (h : PreparedChosenModule T M V)
    (hres : ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
      omegaOneCenterAmbient (ChapterB.thompsonJ (T : Subgroup G) 1) ≤
        centralizer ((pResidual 2 H).map H.subtype : Set G)) :
    ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
      (pResidual 2 H).map H.subtype ≤ centralizer (thompsonFixed T V : Set G) := by
  intro H hH
  exact le_centralizer_iff.mp ((h.thompsonFixed_le_omega T hM).trans (hres H hH))

/-- The normalizer half of15.1.14 uses exactly its preceding residual conclusion. -/
theorem PreparedChosenModule.thompsonFixed_normalizers
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤ centralizer (thompsonFixed T V : Set G)) :
    M ⊓ normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤
        normalizer (thompsonFixed T V : Set G) ∧
      normalizer (thompsonFixed T V : Set G) ≤ Mc ∧
      normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤ M ⊓ Mc := by
  let := h.elementary
  let J := ChapterB.thompsonJ (T : Subgroup G) 1
  let W := thompsonFixed T V
  have hn : M ⊓ normalizer (J : Set G) ≤ normalizer (W : Set G) :=
    (le_inf (inf_le_left.trans h.normalized)
      (inf_le_right.trans (normalizer_le_normalizer_centralizer _))).trans
        inf_normalizer_le_normalizer_inf
  have hTJ : (T : Subgroup G) ≤ normalizer (J : Set G) := by
    intro t ht
    rw [mem_normalizer_iff_map_conj_eq]
    change (ChapterB.thompsonJ (T : Subgroup G) 1).map (MulAut.conj t).toMonoidHom = _
    rw [←ChapterB.thompsonJ_map_equiv]
    exact congrArg (fun S => ChapterB.thompsonJ S 1)
      (mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer ht))
  let C := centralizer (centralInvolutions T : Set G)
  have hTC : (T : Subgroup G) ≤ C := by
    intro t ht z hz
    exact (((mem_omegaOneCenterAmbient_iff _ z).mp hz).2.2 t ht).symm
  have hCN : C ≤ normalizer (W : Set G) := by
    have he := congrArg (map C.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTC))
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le hTC] at he
    rw [←he]
    exact sup_le (hres.trans (Subgroup.centralizer_le_normalizer _)) ((le_inf hM.1.2 hTJ).trans hn)
  have hunique : ∀ L : Subgroup G, IsMaximalTwoLocal L → C ≤ L → L = Mc := by
    intro L hL hCL
    exact Set.mem_singleton_iff.mp (hu ▸ (show L ∈ maximalTwoLocalOvergroups C from ⟨hL,hCL⟩))
  have hWMc : normalizer (W : Set G) ≤ Mc :=
    normalizer_le_of_unique_maximalTwoLocal hunique
      ((IsElementaryAbelian.isPGroup 2 V).to_le inf_le_left)
      (thompsonFixed_nontrivial T h.nontrivial h.seed_span) hCN
  have hJM : normalizer (J : Set G) ≤ M :=
    (normalizer_thompsonJ_le_normalizer_maxJ T
      (chosen_twoRank_gt_one_of_quadraticRatio_two T hM.1.2 h.le_selected
        h.normalized h.quadratic_ratio)).trans
      (source_centralizing_baumann_control hG T hM hJ).2.2.2.2.2.1
  exact ⟨hn,hWMc,le_inf hJM ((le_inf hJM le_rfl).trans (hn.trans hWMc))⟩

end CFSG.Quasithin.Chapter15.Section01
