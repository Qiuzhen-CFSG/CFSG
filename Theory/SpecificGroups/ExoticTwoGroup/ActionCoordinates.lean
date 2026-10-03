module

public import Theory.SpecificGroups.ExoticTwoGroup.ActionModel

/-!
# Coordinate dependence of the exotic swap action

The coordinate change `(x,y) ↦ (-y,x-y)` cycles the three nonidentity
elements of the omega four and preserves the inner action four. However,
an automorphism subgroup of order sixteen cannot contain both the swap
and its image under this change: their product has order three.

Thus specifying the inner four alone does not orient the outer swap.
This distinguishes the choice of basis in MacWilliams, Trans. AMS 150
(1970), §4(xiv), p.393, from the inner-action normalization, in the
argument cited by Janko–Thompson 1.4(c), p.386.
-/

namespace ExoticTwoGroup.ActionModel

open C4SquareExtension Subgroup

private def cycleMap (x : Model) : Model :=
  (Multiplicative.ofAdd (-x.2.toAdd), Multiplicative.ofAdd (x.1.toAdd - x.2.toAdd))

private def cycleInv (x : Model) : Model :=
  (Multiplicative.ofAdd (x.2.toAdd - x.1.toAdd), Multiplicative.ofAdd (-x.1.toAdd))

/-- A coordinate change cycling the three involutions of the omega four. -/
public def coordinateCycle : MulAut Model where
  toFun := cycleMap
  invFun := cycleInv
  left_inv := by decide
  right_inv := by decide
  map_mul' x y := by
    ext <;> simp only [cycleMap, Prod.fst_mul, Prod.snd_mul,
      toAdd_mul, toAdd_ofAdd] <;> ring

private theorem coordinateCycle_u : coordinateCycle u = v := by
  rw [u_eq, v_eq]
  decide

private theorem coordinateCycle_v : coordinateCycle v = u⁻¹ * v⁻¹ := by
  rw [u_eq, v_eq]
  decide

private theorem coordinateCycle_symm_u : coordinateCycle.symm u = u⁻¹ * v⁻¹ := by
  rw [u_eq, v_eq]
  decide

private theorem coordinateCycle_symm_v : coordinateCycle.symm v = u := by
  rw [u_eq, v_eq]
  decide

/-- Cycling coordinates sends the first inner action to the second. -/
public theorem coordinateCycle_inner₁ :
    MulAut.congr coordinateCycle inner₁ = inner₂ := by
  apply aut_ext
  all_goals
    simp only [MulAut.congr_apply, MulEquiv.trans_apply,
      coordinateCycle_symm_u, coordinateCycle_symm_v, map_mul, map_inv,
      inner₁_u, inner₁_v, inner₂_u, inner₂_v,
      map_pow, coordinateCycle_u, coordinateCycle_v]
  all_goals rw [u_eq, v_eq]
  all_goals decide

/-- Cycling coordinates sends the product of the inner actions to the first. -/
public theorem coordinateCycle_inner₁_inner₂ :
    MulAut.congr coordinateCycle (inner₁ * inner₂) = inner₁ := by
  apply aut_ext <;>
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.mul_apply,
      coordinateCycle_symm_u, coordinateCycle_symm_v, map_mul, map_inv,
      inner₁_u, inner₁_v, inner₂_u, inner₂_v,
      map_pow, coordinateCycle_u, coordinateCycle_v] <;>
    rw [u_eq, v_eq] <;> decide

/-- Both prescribed inner actions remain present after cycling coordinates. -/
public theorem inner_mem_coordinateCycle (A : Subgroup (MulAut Model))
    (h₁ : inner₁ ∈ A) (h₂ : inner₂ ∈ A) :
    inner₁ ∈ A.map (MulAut.congr coordinateCycle).toMonoidHom ∧
      inner₂ ∈ A.map (MulAut.congr coordinateCycle).toMonoidHom := by
  constructor
  · rw [← coordinateCycle_inner₁_inner₂]
    exact mem_map_of_mem _ (A.mul_mem h₁ h₂)
  · rw [← coordinateCycle_inner₁]
    exact mem_map_of_mem _ h₁

/-- The coordinate cycle has order three. -/
public theorem orderOf_coordinateCycle : orderOf coordinateCycle = 3 := by
  apply orderOf_eq_prime
  · apply aut_ext <;>
      simp only [pow_succ, pow_zero, MulAut.mul_apply, MulAut.one_apply,
        coordinateCycle_u, coordinateCycle_v, map_mul, map_inv] <;>
      rw [u_eq, v_eq] <;> decide
  · intro h
    exact (by rw [u_eq]; decide : coordinateCycle u ≠ u)
      (congrArg (fun f : MulAut Model => f u) h)

private theorem not_coordinateCycle_swap_mem (A : Subgroup (MulAut Model))
    (hA : Nat.card A = 16) (ht : swap ∈ A) :
    MulAut.congr coordinateCycle swap ∉ A := by
  intro ht'
  have hc : coordinateCycle ∈ A := by
    have he : swap * (MulAut.congr coordinateCycle swap) = coordinateCycle := by
      apply aut_ext <;>
        simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.mul_apply,
          coordinateCycle_symm_u, coordinateCycle_symm_v, map_mul, map_inv,
          swap_u, swap_v, coordinateCycle_u, coordinateCycle_v] <;>
        rw [u_eq, v_eq] <;> decide
    rw [← he]
    exact A.mul_mem ht ht'
  have hd := A.orderOf_dvd_natCard hc
  rw [orderOf_coordinateCycle, hA] at hd
  norm_num at hd

/-- If an order-sixteen image contains swap, its cycled image does not. -/
public theorem swap_not_mem_coordinateCycle (A : Subgroup (MulAut Model))
    (hA : Nat.card A = 16) (ht : swap ∈ A) :
    swap ∉ A.map (MulAut.congr coordinateCycle).toMonoidHom := by
  intro hm
  have hcard : Nat.card (A.map (MulAut.congr coordinateCycle).toMonoidHom) = 16 := by
    rw [card_map_of_injective (MulAut.congr coordinateCycle).injective, hA]
  exact not_coordinateCycle_swap_mem _ hcard hm (mem_map_of_mem _ ht)

end ExoticTwoGroup.ActionModel
