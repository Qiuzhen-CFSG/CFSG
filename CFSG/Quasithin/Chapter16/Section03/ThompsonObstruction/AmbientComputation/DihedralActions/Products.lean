module

public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.AmbientComputation.Contracts
public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.AmbientComputation.RankGeometry.MarkedAction
public import Theory.GroupTheory.DisjointCommutingProduct

@[expose] public section

namespace CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation

/-!
# Compatible products for the marked Thompson calculation

The marked transposition action proves that the component factor and either
source candidate are jointly disjoint from the centralizer factor. This gives
ambient multiplication equivalences for the relevant internal products. The
source-specific action alternatives and maximum-elementary generation are
assembled in `MaxJClassification` and re-exported by `DihedralActions`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Lemma 16.3.12,
printed pp.1181–1182 / PDF pp.1198–1199.
-/
open Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] {T : Sylow 2 G} {z t : G} {L : Subgroup G}

theorem markedAction_eq_one_of_commuting (d : Prepared T z t L) {x : G}
    (hx : x ∈ commutingSylow T L) : markedAction d ⟨x, hx.1⟩ = 1 := by
  change (⟨x, hx.1⟩ : T) ∈ (markedAction d).ker
  rw [markedAction_ker]
  exact hx

theorem candidate_markedAction (d : Prepared T z t L) {w : G}
    (hw : w = d.marked.u ∨ w = t * d.marked.u) :
    markedAction d ⟨w, (candidate_mem_and_centralizes d hw).1⟩ =
      AlternatingSix.ShadowLocal.permutationAction (Equiv.swap (0 : Fin 6) 1) := by
  rcases hw with rfl | rfl
  · exact markedAction_u d
  · change markedAction d (⟨t, d.counterexample.mem_commutingSylow.1⟩ *
      ⟨d.marked.u, d.u_mem⟩) = _
    rw [map_mul, markedAction_eq_one_of_commuting d d.counterexample.mem_commutingSylow,
      one_mul, markedAction_u]

theorem candidate_markedAction_not_inner (d : Prepared T z t L) {w : G}
    (hw : w = d.marked.u ∨ w = t * d.marked.u) :
    markedAction d ⟨w, (candidate_mem_and_centralizes d hw).1⟩ ∉
      AlternatingSix.ShadowLocal.inner := by
  rw [candidate_markedAction d hw]
  exact MarkedAction.transposition_not_inner

private theorem zpowers_two_cases {x w : G} (hw : orderOf w = 2)
    (hx : x ∈ zpowers w) : x = 1 ∨ x = w := by
  classical
  have hf : IsOfFinOrder w := orderOf_pos_iff.mp (by omega)
  rw [hf.mem_zpowers_iff_mem_range_orderOf, hw] at hx
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hx
  have hnlt : n < 2 := Finset.mem_range.mp hn
  interval_cases n
  · exact Or.inl (by simpa only [pow_zero] using he.symm)
  · exact Or.inr (by simpa only [pow_one] using he.symm)

theorem commutingSylow_disjoint_component_candidate (d : Prepared T z t L) {w : G}
    (hw : w = d.marked.u ∨ w = t * d.marked.u) :
    Disjoint (commutingSylow T L) (componentSylow T L ⊔ zpowers w) := by
  have hwT := (candidate_mem_and_centralizes d hw).1
  have hwC := (candidate_mem_and_centralizes d hw).2
  have hn : zpowers w ≤ normalizer (componentSylow T L : Set G) :=
    (zpowers_le.mpr hwC).trans (Subgroup.centralizer_le_normalizer _)
  apply Subgroup.disjoint_def.mpr
  intro x hx hx'
  have hx'' : x ∈ (componentSylow T L : Set G) * (zpowers w : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hn]
    exact hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := hx''
  rcases zpowers_two_cases (candidate_order d hw) hb with hb1 | hbw
  · subst b
    have haK : a ∈ commutingSylow T L := by simpa only [mul_one] using hx
    have h : markedComponentAction d ⟨a, ha⟩ = markedComponentAction d 1 := by
      rw [map_one]
      exact markedAction_eq_one_of_commuting d haK
    have he := congrArg (fun a : componentSylow T L => (a : G))
      (markedComponentAction_injective d h)
    simpa only [mul_one, Subgroup.coe_one] using he
  · subst b
    have hp : markedAction d ⟨a, ha.1⟩ * markedAction d ⟨w, hwT⟩ = 1 := by
      rw [← map_mul]
      exact markedAction_eq_one_of_commuting d hx
    have he : markedAction d ⟨w, hwT⟩ = (markedAction d ⟨a, ha.1⟩)⁻¹ :=
      eq_inv_of_mul_eq_one_right hp
    have hi : markedAction d ⟨a, ha.1⟩ ∈ AlternatingSix.ShadowLocal.inner :=
      markedComponentAction_le_inner d ⟨⟨a, ha⟩, rfl⟩
    exact (candidate_markedAction_not_inner d hw
      (he.symm ▸ AlternatingSix.ShadowLocal.inner.inv_mem hi)).elim

theorem component_disjoint_candidate (d : Prepared T z t L) {w : G}
    (hw : w = d.marked.u ∨ w = t * d.marked.u) :
    Disjoint (componentSylow T L) (zpowers w) := by
  apply Subgroup.disjoint_def.mpr
  intro x hx hx'
  rcases zpowers_two_cases (candidate_order d hw) hx' with h | h
  · exact h
  · subst x
    exact (candidate_markedAction_not_inner d hw
      (markedComponentAction_le_inner d ⟨⟨w, hx⟩, rfl⟩)).elim

theorem exists_candidate_product (d : Prepared T z t L) {w : G}
    (hw : w = d.marked.u ∨ w = t * d.marked.u) (R : Subgroup G)
    (hR : R ≤ commutingSylow T L) (hRw : w ∈ centralizer (R : Set G)) :
    ∃ e : (R × componentSylow T L × zpowers w) ≃*
        ↥(R ⊔ componentSylow T L ⊔ zpowers w),
      ∀ (a : R) (b : componentSylow T L) (c : zpowers w),
        (e (a, b, c) : G) = (a : G) * (b : G) * (c : G) := by
  have hCW : componentSylow T L ≤ centralizer (zpowers w : Set G) := by
    exact le_centralizer_iff.mpr (zpowers_le.mpr
      (candidate_mem_and_centralizes d hw).2)
  obtain ⟨eCW, heCW⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    (componentSylow T L) (zpowers w) (component_disjoint_candidate d hw) hCW
  have hRC : R ≤ centralizer (componentSylow T L : Set G) :=
    hR.trans (inf_le_right.trans (centralizer_le (show componentSylow T L ≤ L from inf_le_right)))
  have hRW : R ≤ centralizer (zpowers w : Set G) := by
    exact le_centralizer_iff.mpr (zpowers_le.mpr hRw)
  have hc : R ≤ centralizer ((componentSylow T L ⊔ zpowers w : Subgroup G) : Set G) := by
    exact le_centralizer_iff.mpr
      (sup_le (le_centralizer_iff.mp hRC) (le_centralizer_iff.mp hRW))
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting R
    (componentSylow T L ⊔ zpowers w)
    ((commutingSylow_disjoint_component_candidate d hw).mono_left hR) hc
  refine ⟨((MulEquiv.prodCongr (MulEquiv.refl R) eCW).trans e).trans
    (MulEquiv.subgroupCongr (sup_assoc _ _ _).symm), ?_⟩
  intro a b c
  change (e (a, eCW (b, c)) : G) = _
  rw [he, heCW, mul_assoc]

theorem smallGroup_eq_candidate_join (d : Prepared T z t L) {w : G}
    (hw : w = d.marked.u ∨ w = t * d.marked.u) :
    smallGroup d = commutingSylow T L ⊔ componentSylow T L ⊔ zpowers w := by
  rcases hw with rfl | rfl
  · rfl
  · have ht : t ∈ commutingSylow T L ⊔ componentSylow T L :=
      mem_sup_left d.counterexample.mem_commutingSylow
    apply le_antisymm
    · apply sup_le le_sup_left
      apply zpowers_le.mpr
      have ht' := (le_sup_left : commutingSylow T L ⊔ componentSylow T L ≤
        commutingSylow T L ⊔ componentSylow T L ⊔ zpowers (t * d.marked.u)) ht
      have htu : t * d.marked.u ∈ commutingSylow T L ⊔ componentSylow T L ⊔
          zpowers (t * d.marked.u) := mem_sup_right (mem_zpowers (t * d.marked.u))
      simpa only [inv_mul_cancel_left] using
        (commutingSylow T L ⊔ componentSylow T L ⊔ zpowers (t * d.marked.u)).mul_mem
          ((commutingSylow T L ⊔ componentSylow T L ⊔ zpowers (t * d.marked.u)).inv_mem ht') htu
    · apply sup_le le_sup_left
      apply zpowers_le.mpr
      exact (smallGroup d).mul_mem (mem_sup_left ht)
        (mem_sup_right (mem_zpowers d.marked.u))

theorem sylow_normalizes_commutingSylow (d : Prepared T z t L) :
    (T : Subgroup G) ≤ normalizer (commutingSylow T L : Set G) := by
  intro x hx
  exact inf_normalizer_le_normalizer_inf
    ⟨(T : Subgroup G).le_normalizer hx,
      normalizer_le_normalizer_centralizer L (d.counterexample.sylow_le_normalizer hx)⟩

theorem candidate_tail_disjoint_component (d : Prepared T z t L) {w : G}
    (hw : w = d.marked.u ∨ w = t * d.marked.u) :
    Disjoint (commutingSylow T L ⊔ zpowers w) (componentSylow T L) := by
  have hn : zpowers w ≤ normalizer (commutingSylow T L : Set G) :=
    (zpowers_le.mpr (candidate_mem_and_centralizes d hw).1).trans
      (sylow_normalizes_commutingSylow d)
  apply Subgroup.disjoint_def.mpr
  intro x hx hxC
  have hx' : x ∈ (commutingSylow T L : Set G) * (zpowers w : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hn]
    exact hx
  obtain ⟨a, ha, b, hb, hab⟩ := hx'
  have ha' : a ∈ componentSylow T L ⊔ zpowers w := by
    have hm := (componentSylow T L ⊔ zpowers w).mul_mem
      (mem_sup_left hxC) (mem_sup_right ((zpowers w).inv_mem hb))
    rw [← hab, mul_inv_cancel_right] at hm
    exact hm
  have ha1 := Subgroup.disjoint_def.mp (commutingSylow_disjoint_component_candidate d hw) ha ha'
  have hbx : b = x := by simpa only [ha1, one_mul] using hab
  exact Subgroup.disjoint_def.mp (component_disjoint_candidate d hw) hxC (hbx ▸ hb)

theorem exists_smallGroup_tail_product (d : Prepared T z t L) {w : G}
    (hw : w = d.marked.u ∨ w = t * d.marked.u) :
    ∃ e : (↥(commutingSylow T L ⊔ zpowers w) × componentSylow T L) ≃* smallGroup d,
      ∀ a b, (e (a, b) : G) = (a : G) * (b : G) := by
  have hc : commutingSylow T L ⊔ zpowers w ≤ centralizer (componentSylow T L : Set G) :=
    sup_le (inf_le_right.trans (centralizer_le (show componentSylow T L ≤ L from inf_le_right)))
      (zpowers_le.mpr (candidate_mem_and_centralizes d hw).2)
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    (commutingSylow T L ⊔ zpowers w) (componentSylow T L)
    (candidate_tail_disjoint_component d hw) hc
  have hjoin : (commutingSylow T L ⊔ zpowers w) ⊔ componentSylow T L = smallGroup d := by
    rw [smallGroup_eq_candidate_join d hw]
    exact sup_right_comm _ _ _
  exact ⟨e.trans (MulEquiv.subgroupCongr hjoin), he⟩
end CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation
