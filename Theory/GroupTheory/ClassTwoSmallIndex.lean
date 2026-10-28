module
public import Theory.GroupTheory.ClassTwoCommutator
public import Mathlib.Algebra.Group.Subgroup.Finite
import Lean.Elab.Tactic.Omega
/-!
# Small-index subgroups in groups of class two

An abelian subgroup of index at most four gives two additional generators.
Intersecting its centralizers of those generators bounds the center index
by the index of the subgroup times the square of the derived-group order.
This bound is used to recover the whole derived group from an index-four
subgroup in the natural symplectic extension of MS93 (3.10), pp.880--881.
-/
public section
open Subgroup
open scoped commutatorElement
set_option linter.style.haveILetI false
namespace Subgroup.ClassTwo
variable {G : Type*} [Group G] [Finite G]

private theorem exists_two_generators_mod_index_four
    (A : Subgroup G) (hi : A.index ≤ 4) :
    ∃ x y : G, A ⊔ zpowers x ⊔ zpowers y = ⊤ := by
  classical
  by_cases ht : A = ⊤
  · exact ⟨1,1,by simp [ht]⟩
  obtain ⟨x,hx⟩ : ∃ x : G, x ∉ A := by
    by_contra! h
    exact ht (top_unique (fun x _ => h x))
  let B := A ⊔ zpowers x
  letI : A.IsFiniteRelIndex B := Subgroup.isFiniteRelIndex_of_finiteIndex
  have hAB : A < B := lt_of_le_of_ne le_sup_left (by
    intro he
    exact hx (he ▸ (mem_sup_right (mem_zpowers x) : x ∈ B)))
  have hrel : 2 ≤ A.relIndex B := by
    have hpos : 0 < A.relIndex B := Nat.pos_of_ne_zero relIndex_ne_zero
    have hne : A.relIndex B ≠ 1 := fun h =>
      hAB.not_ge (relIndex_eq_one.mp h)
    omega
  have hBi : B.index ≤ 2 := by
    have hm := Nat.mul_le_mul_right B.index hrel
    rw [relIndex_mul_index hAB.le] at hm
    omega
  by_cases hBt : B = ⊤
  · exact ⟨x,1,by change B ⊔ zpowers 1 = ⊤; rw [hBt,top_sup_eq]⟩
  obtain ⟨y,hy⟩ : ∃ y : G, y ∉ B := by
    by_contra! h
    exact hBt (top_unique (fun y _ => h y))
  let C := B ⊔ zpowers y
  have hBC : B < C := lt_of_le_of_ne le_sup_left (by
    intro he
    exact hy (he ▸ (mem_sup_right (mem_zpowers y) : y ∈ C)))
  have hiC := index_strictAnti hBC
  have hpos : 0 < C.index := Nat.pos_of_ne_zero C.index_ne_zero_of_finite
  exact ⟨x,y,index_eq_one.mp (by omega : C.index = 1)⟩

/-- An abelian subgroup of index at most four bounds the central quotient
when the derived subgroup is central of order at most four. -/
theorem center_index_le_sixtyFour_of_abelian_index_le_four
    (hc : _root_.commutator G ≤ center G)
    (hd : Nat.card (_root_.commutator G) ≤ 4)
    (A : Subgroup G) [IsMulCommutative A] (hi : A.index ≤ 4) :
    (center G).index ≤ 64 := by
  obtain ⟨x,y,hgen⟩ := exists_two_generators_mod_index_four A hi
  let Z := A ⊓ centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G)
  have hZ : Z ≤ center G := by
    rintro z ⟨⟨hz,hzx⟩,hzy⟩
    have hA : A ≤ centralizer ({z} : Set G) := by
      intro a ha
      exact mem_centralizer_singleton_iff.mpr (A.le_centralizer hz a ha)
    have hx : zpowers x ≤ centralizer ({z} : Set G) := by
      apply zpowers_le.mpr
      exact mem_centralizer_singleton_iff.mpr
        ((mem_centralizer_singleton_iff.mp hzx).symm)
    have hy : zpowers y ≤ centralizer ({z} : Set G) := by
      apply zpowers_le.mpr
      exact mem_centralizer_singleton_iff.mpr
        ((mem_centralizer_singleton_iff.mp hzy).symm)
    have ht : (⊤ : Subgroup G) ≤ centralizer ({z} : Set G) := by
      rw [←hgen]
      exact sup_le (sup_le hA hx) hy
    apply mem_center_iff.mpr
    intro g
    exact mem_centralizer_singleton_iff.mp (ht (mem_top g))
  have hix : (centralizer ({x} : Set G)).index ≤ 4 := by
    rw [centralizer_index hc x]
    exact (card_le_of_le (commutator_mono le_top le_rfl)).trans hd
  have hiy : (centralizer ({y} : Set G)).index ≤ 4 := by
    rw [centralizer_index hc y]
    exact (card_le_of_le (commutator_mono le_top le_rfl)).trans hd
  have hZidx : Z.index ≤ (A.index * (centralizer ({x} : Set G)).index) *
      (centralizer ({y} : Set G)).index :=
    index_inf_le.trans (Nat.mul_le_mul_right _ index_inf_le)
  exact (index_antitone hZ).trans (hZidx.trans
    (Nat.mul_le_mul (Nat.mul_le_mul hi hix) hiy))

/-- Full nonzero commutator rows force every index-four subgroup to have
exactly the ambient derived subgroup. -/
theorem derived_eq_of_index_le_four_of_full_rows
    (hc : _root_.commutator G ≤ center G)
    (hd : Nat.card (_root_.commutator G) ≤ 4)
    (N : Subgroup G) (hN : 64 < N.index)
    (hrow : ∀ x : G, x ∉ N → _root_.commutator G = ⁅zpowers x,⊤⁆)
    (A : Subgroup G) (hi : A.index ≤ 4) :
    ⁅A,A⁆ = _root_.commutator G := by
  let D : Subgroup G := ⁅A,A⁆
  have hD : D ≤ _root_.commutator G := commutator_mono le_top le_top
  have hDc : D ≤ center G := hD.trans hc
  let : D.Normal := ⟨fun x hx g => by
    rw [mem_center_iff.mp (hDc hx) g, mul_inv_cancel_right]
    exact hx⟩
  let q := QuotientGroup.mk' D
  have hq := QuotientGroup.mk'_surjective D
  have hder : (_root_.commutator G).map q = _root_.commutator (G ⧸ D) := by
    rw [map_commutator_eq,q.range_eq_top_of_surjective hq]
    rfl
  have hquot : _root_.commutator (G ⧸ D) ≤ center (G ⧸ D) := by
    rw [← hder]
    rintro _ ⟨x,hx,rfl⟩
    apply mem_center_iff.mpr
    intro y
    obtain ⟨z,rfl⟩ := hq y
    simpa only [map_mul,q] using congrArg q (mem_center_iff.mp (hc hx) z)
  have hdquot : Nat.card (_root_.commutator (G ⧸ D)) ≤ 4 := by
    rw [← hder]
    exact (Nat.card_le_card_of_surjective _ (q.subgroupMap_surjective _)).trans hd
  have hAquot : IsMulCommutative (A.map q) := by
    apply commutator_self_eq_bot_iff.mp
    rw [← map_commutator]
    exact (map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk'])
  let := hAquot
  have hiquot : (A.map q).index ≤ 4 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero A.index_ne_zero_of_finite)
      (A.index_map_dvd hq)).trans hi
  have hb := center_index_le_sixtyFour_of_abelian_index_le_four hquot hdquot (A.map q) hiquot
  apply le_antisymm hD
  by_contra hnot
  have hcent : (center (G ⧸ D)).comap q ≤ N := by
    intro x hx
    by_contra hxN
    apply hnot
    rw [hrow x hxN]
    rw [← QuotientGroup.ker_mk' D]
    apply (map_eq_bot_iff (f := q) _).mp
    rw [map_commutator,map_top_of_surjective q hq,MonoidHom.map_zpowers]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rw [coe_top,centralizer_univ]
    exact zpowers_le.mpr hx
  have hidx := index_antitone hcent
  rw [index_comap_of_surjective _ hq] at hidx
  omega
end Subgroup.ClassTwo
