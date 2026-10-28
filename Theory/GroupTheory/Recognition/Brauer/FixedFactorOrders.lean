module
public import Theory.GroupTheory.Recognition.Brauer.PlaneData

/-!
# Equal orders of Brauer's fixed subgroups

In Brauer, *On finite Desarguesian planes I*, equation (2.5), p. 119,
postulate (III) supplies an element of `C(j)` conjugating `j2` to `j1`.
Postulate (II) says this element normalizes both `M` and `Mstar`, so its
conjugation restricts to bijections `M2 ≃ M1` and `Mstar2 ≃ Mstar1`.
Consequently each pair has equal orders. This step uses the actual fixed
subgroups defined from the seed; it does not assume the direct-product
factorizations or their later square-order consequences.
-/

namespace Theory.GroupTheory

private theorem card_fixed_subgroups_conj {G : Type*} [Group G]
    (M : Subgroup G) {a b c : G}
    (hc : c ∈ Subgroup.normalizer (M : Set G))
    (hab : c⁻¹ * a * c = b) :
    Nat.card ↥(M ⊓ Subgroup.centralizer {a}) =
      Nat.card ↥(M ⊓ Subgroup.centralizer {b}) := by
  let f : G ≃* G := MulAut.conj c⁻¹
  have hf : f a = b := by simpa only [f, MulAut.conj_apply, inv_inv] using hab
  apply Nat.card_congr (Equiv.subtypeEquiv f.toEquiv ?_)
  intro x
  have hm : x ∈ M ↔ f x ∈ M := by
    simpa only [f, MulAut.conj_apply, inv_inv, SetLike.mem_coe] using
      ((Subgroup.normalizer (M : Set G)).inv_mem hc x)
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]
  refine and_congr hm ?_
  constructor
  · intro h
    have hmap := congrArg f h
    simpa only [map_mul, hf] using hmap
  · intro h
    apply f.injective
    simpa only [map_mul, hf] using h

namespace BrauerPlaneSeed

variable {G : Type*} [Group G] [Finite G]

/-- Brauer I (2.5): the two fixed subgroups in each of `M` and `Mstar`
have equal orders, by conjugation inside the centralizer of `j`. -/
public theorem fixed_factor_card_eq (S : BrauerPlaneSeed G) :
    Nat.card S.M1 = Nat.card S.M2 ∧ Nat.card S.Mstar1 = Nat.card S.Mstar2 := by
  have hj2 : orderOf S.j2 = 2 := by
    have h : (MulAut.conj S.y⁻¹) S.j1 = S.j2 := by
      simpa only [MulAut.conj_apply, inv_inv] using S.y_conj_j1
    rw [← h, MulEquiv.orderOf_eq, S.j1_order]
  have hcomm : Commute S.j2 S.j :=
    (Commute.refl S.j).mul_left S.j_commute_j1.symm
  have hne : S.j2 ≠ S.j := by
    intro h
    have h1 : S.j1 = 1 := mul_left_cancel (show S.j * S.j1 = S.j * 1 by simpa using h)
    have ho := S.j1_order
    simp [h1] at ho
  obtain ⟨c, hc⟩ := S.centralizer_involutions_conjugate S.j2 hj2 hcomm hne
  exact ⟨(card_fixed_subgroups_conj S.M
      (S.centralizer_le_normalizer_M c.property) hc).symm,
    (card_fixed_subgroups_conj S.Mstar
      (S.centralizer_le_normalizer_Mstar c.property) hc).symm⟩

end BrauerPlaneSeed
end Theory.GroupTheory
