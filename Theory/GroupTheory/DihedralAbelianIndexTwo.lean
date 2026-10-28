module
public import Theory.GroupTheory.SemidihedralStandardModel
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Index

/-!
# Abelian index two in dihedral and semidihedral models

The cyclic rotation subgroup has half the order of the group. Transporting
it along a model equivalence supplies an actual abelian subgroup of index
two. This is the only model feature needed by the nonabelian crossing-mark
argument in Aschbacher--Smith 2.5.21, printed p.566.
-/

public section
namespace Subgroup
/-- Every finite dihedral model has an abelian subgroup of index two. -/
theorem exists_abelian_index_two_of_dihedral {P : Type*} [Group P]
    {n : ℕ} (e : P ≃* DihedralGroup (2 ^ n)) :
    ∃ A : Subgroup P, IsMulCommutative A ∧ A.index = 2 := by
  let R := zpowers (DihedralGroup.r 1 : DihedralGroup (2 ^ n))
  have hi : R.index = 2 := by
    have h := R.index_mul_card
    rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one, DihedralGroup.nat_card] at h
    exact Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ n) h
  refine ⟨R.map e.symm.toMonoidHom, inferInstance, ?_⟩
  exact (index_map_of_bijective e.symm.bijective R).trans hi

/-- The semidihedral sixteen model has its cyclic rotations of index two. -/
theorem exists_abelian_index_two_of_semidihedral_sixteen {P : Type*} [Group P]
    (e : P ≃* Semidihedral.StandardModel 4 (by decide)) :
    ∃ A : Subgroup P, IsMulCommutative A ∧ A.index = 2 := by
  let R := zpowers (Semidihedral.standardRotation 4 (by decide))
  have hi : R.index = 2 := by
    have h := R.index_mul_card
    rw [Nat.card_zpowers, Semidihedral.standardRotation_order, Semidihedral.standardModel_card] at h
    norm_num at h ⊢
    omega
  refine ⟨R.map e.symm.toMonoidHom, inferInstance, ?_⟩
  exact (index_map_of_bijective e.symm.bijective R).trans hi

end Subgroup
