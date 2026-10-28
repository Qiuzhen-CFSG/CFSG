module
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus
public import Theory.GroupTheory.WreathTwoIndexTwo
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# The index-two alternative in the full binary plus orthogonal group

The actual binary plus orthogonal group is identified with the two-plane
wreath group. A subgroup of index at most two containing an elementary
four-group is either the full group or has a normal cubic subgroup. The
proof transports the marked subgroup and its four-group through the
existing isometry equivalence and retains the original subgroup as the
domain of the resulting normal cubic.

Source application: Aschbacher--Smith 14.3.15, degree four, together with
G.9.4(4). The normal-cubic exclusion belongs to the original local setup.
-/

open Subgroup
namespace BinaryFourPlus

/-- An index-two subgroup with a marked elementary four has a normal cubic. -/
public theorem normal_cubic_of_index_two
    (H A : Subgroup q.isometrySubgroup) (hi : H.index=2)
    [IsElementaryAbelian 2 A] (hAH : A≤H) (hA : Nat.card A=4) :
    ∃ C : Subgroup H, C.Normal ∧ Nat.card C=3 := by
  obtain ⟨eSL⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  let e := isometryEquivWreath.trans
    (RegularWreathProduct.congr eSL.symm (MulEquiv.refl C2))
  let H' := H.map e.toMonoidHom
  let A' := A.map e.toMonoidHom
  let : IsElementaryAbelian 2 A' := IsElementaryAbelian.map (A:=A) e.toMonoidHom
  have hA' : Nat.card A'=4 := (card_map_of_injective e.injective).trans hA
  obtain ⟨C,hCn,hCc⟩ := Theory.GroupTheory.WreathTwoIndexTwo.normal_cubic_of_index_two
    H' A' ((index_map_of_bijective e.bijective H).trans hi) (map_mono hAH) hA'
  let f : H≃*H' := e.subgroupMap H
  refine ⟨C.map f.symm.toMonoidHom,hCn.map _ f.symm.surjective,?_⟩
  exact (card_map_of_injective f.symm.injective).trans hCc

/-- The full-action alternative retains the actual orthogonal subgroup. -/
public theorem eq_top_or_normal_cubic_of_index_le_two
    (H A : Subgroup q.isometrySubgroup) (hi : H.index≤2)
    [IsElementaryAbelian 2 A] (hAH : A≤H) (hA : Nat.card A=4) :
    H=⊤ ∨ ∃ C : Subgroup H, C.Normal ∧ Nat.card C=3 := by
  by_cases htop : H=⊤
  · exact Or.inl htop
  · right
    let : Finite q.isometrySubgroup := Nat.finite_of_card_ne_zero (by rw [card_isometrySubgroup]; decide)
    have hpos : 0<H.index := Nat.pos_of_ne_zero H.index_ne_zero_of_finite
    have hne : H.index≠1 := mt H.index_eq_one.mp htop
    exact normal_cubic_of_index_two H A (by omega) hAH hA
end BinaryFourPlus
