module

public import Theory.GroupTheory.ElementaryEightPlaneOrder24

/-!
# Point stabilizers in the full elementary-eight plane stabilizer

Fixing a point outside the invariant four-group leaves a faithful action
on the other three outside points. The known stabilizer order six makes
this action the full symmetric group.

Source: the elementary affine action underlying Parrott,
*A characterization of the Tits' simple group* (1972), pp.677 and 682.
-/

open Subgroup

/-- A point stabilizer outside the invariant plane is the symmetric group
on three letters. -/
public theorem elementaryEight_plane_order24_outside_stabilizer_equiv_S3
    {U : Type*} [Group U] [Finite U] [IsElementaryAbelian 2 U]
    (hU : Nat.card U = 8) (W : Subgroup U) (hW : Nat.card W = 4)
    (A : Subgroup (MulAut U)) (hA : Nat.card A = 24)
    (hstable : ∀ a : A, ∀ y : U, (a : MulAut U) y ∈ W ↔ y ∈ W)
    (x : U) (hx : x ∉ W) :
    Nonempty (MulAction.stabilizer A x ≃* Equiv.Perm (Fin 3)) := by
  classical
  let S := MulAction.stabilizer A x
  let X := {y : U // y ∉ W ∧ y ≠ x}
  have hX : Nat.card X = 3 := by
    change (((W : Set U)ᶜ \ {x}).ncard) = 3
    rw [Set.ncard_sdiff_singleton_of_mem hx, Set.ncard_compl]
    change Nat.card U - Nat.card W - 1 = 3
    rw [hU, hW]
  have hpres (a : S) (y : U) :
      (a.val.val : MulAut U) y ∉ W ∧ (a.val.val : MulAut U) y ≠ x ↔
        y ∉ W ∧ y ≠ x := by
    have hax : (a.val.val : MulAut U) x = x := a.property
    have hne : (a.val.val : MulAut U) y ≠ x ↔ y ≠ x := by
      constructor
      · intro hh heq
        exact hh (heq ▸ hax)
      · intro hh heq
        exact hh ((a.val.val : MulAut U).injective (heq.trans hax.symm))
    exact and_congr (not_congr (hstable a.val y)) hne
  let r : S →* Equiv.Perm X := {
    toFun a := Equiv.Perm.subtypePerm (a.val.val : MulAut U).toEquiv (hpres a)
    map_one' := by ext y; rfl
    map_mul' a b := by ext y; rfl }
  have hinj : Function.Injective r := by
    intro a b hab
    have hout (y : U) (hy : y ∉ W) :
        (a.val.val : MulAut U) y = (b.val.val : MulAut U) y := by
      by_cases hyx : y = x
      · subst y
        exact a.property.trans b.property.symm
      · exact congrArg Subtype.val (Equiv.congr_fun hab ⟨y, hy, hyx⟩)
    apply Subtype.ext
    apply Subtype.ext
    apply MulEquiv.ext
    intro y
    by_cases hy : y ∈ W
    · have hyx : y * x ∉ W := by
        intro hh
        exact hx (by simpa only [inv_mul_cancel_left] using W.mul_mem (W.inv_mem hy) hh)
      have hh := hout (y * x) hyx
      rw [map_mul, map_mul, hout x hx] at hh
      exact mul_right_cancel hh
    · exact hout y hy
  have hS : Nat.card S = 6 :=
    elementaryEight_plane_order24_outside_stabilizer_card hU W hW A hA hstable x hx
  let : Fintype X := Fintype.ofFinite X
  have hperm : Nat.card (Equiv.Perm X) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card, hX]
    decide
  exact ⟨(MulEquiv.ofBijective r
    ((Nat.bijective_iff_injective_and_card r).mpr ⟨hinj, hS.trans hperm.symm⟩)).trans
    (Equiv.permCongrHom (Finite.equivFinOfCardEq hX))⟩
