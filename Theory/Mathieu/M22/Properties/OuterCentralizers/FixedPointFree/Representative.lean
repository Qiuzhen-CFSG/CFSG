module

public import Theory.Mathieu.M22.Properties.OuterCentralizers.DesignAction
public import Theory.Mathieu.M22.Properties.CubicInverters.Enumeration

/-!
# A marked fixed-point-free outer involution of M₂₂

Row 24 of the certified design-group Sylow subgroup is an odd involution
moving every point of the degree-22 action. Its explicit permutation table
provides the common representative for the centralizer and conjugacy
calculations. Membership in the design group comes from the existing word
certificate, rather than from a class label.

Source: Aschbacher–Smith 16.1.5(5), combined manuscript, printed p.1171.
-/

@[expose] public section
namespace Sporadic.Mathieu.M22OuterCentralizers.FixedPointFree

/-- The fixed-point-free involution in the existing certified Sylow model. -/
noncomputable def representative : m22DesignAut := M22CubicInverters.rowElement 24

/-- Its point table, in the original `Fin 22` labels. -/
def representativeTable : Fin 22 → Fin 22 :=
  ![4,2,1,20,0,12,16,17,21,15,18,19,5,14,13,9,6,7,10,11,3,8]

theorem representative_apply (x : Fin 22) :
    representative.val x = representativeTable x := by
  rw [representative, M22CubicInverters.rowElement_apply]
  revert x
  decide +kernel

private theorem square_eq_one_of_table (s : m22DesignAut)
    (h : ∀ x : Fin 22, s.val x = representativeTable x) : s ^ 2 = 1 := by
  rw [pow_two]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_one]
  apply Equiv.ext
  intro x
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, h]
  revert x
  decide +kernel

theorem representative_sq : representative ^ 2 = 1 :=
  square_eq_one_of_table representative representative_apply

theorem representative_order : orderOf representative = 2 := by
  apply orderOf_eq_prime representative_sq
  intro h
  have hf := congrArg (fun g : m22DesignAut => g.val 0) h
  rw [representative_apply] at hf
  exact (by decide : representativeTable 0 ≠ (0 : Fin 22)) hf

theorem representative_moves (x : Fin 22) : representative.val x ≠ x := by
  rw [representative_apply]
  revert x
  decide +kernel

theorem representative_fixedPoints_card : (fixedPoints representative).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact representative_moves x ((mem_fixedPoints _ _).mp hx)

private theorem representative_perm :
    representative.val =
      Equiv.swap 0 4 * Equiv.swap 1 2 * Equiv.swap 3 20 *
      Equiv.swap 5 12 * Equiv.swap 6 16 * Equiv.swap 7 17 *
      Equiv.swap 8 21 * Equiv.swap 9 15 * Equiv.swap 10 18 *
      Equiv.swap 11 19 * Equiv.swap 13 14 := by
  apply Equiv.ext
  intro x
  rw [representative_apply]
  revert x
  decide +kernel

theorem representative_outer : (representative : Equiv.Perm (Fin 22)) ∉ M22 := by
  intro h
  have he := M22_le_alternatingGroup h
  rw [Equiv.Perm.mem_alternatingGroup] at he
  have hsign : Equiv.Perm.sign representative.val = -1 := by
    rw [representative_perm]
    decide +kernel
  rw [hsign] at he
  exact (by decide : (-1 : ℤˣ) ≠ 1) he

end Sporadic.Mathieu.M22OuterCentralizers.FixedPointFree
