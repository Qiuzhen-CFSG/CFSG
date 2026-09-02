module

public import Theory.GroupAction.Defs

namespace Theory.GroupAction

/-- A quadratic action fixes its first action-commutator subgroup pointwise. -/
public theorem commutatorAction_le_fixedPoints_of_commutatorAction₂_eq_bot
    {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    (hquadratic : commutatorAction₂ A G = ⊥) :
    commutatorAction A G ≤ FixedPoints.subgroup A G := by
  intro d hd
  rw [FixedPoints.mem_subgroup]
  intro a
  have hdelta : d⁻¹ * (a • d) ∈ commutatorAction₂ A G := by
    exact Subgroup.subset_closure ⟨a, d, hd, rfl⟩
  have hone : d⁻¹ * (a • d) = 1 := by
    rw [hquadratic] at hdelta
    simpa using hdelta

end Theory.GroupAction
  exact (eq_of_inv_mul_eq_one hone).symm
