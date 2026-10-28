module
public import Theory.SpecificGroups.PSL2.OuterSolvable.SmallDegreeSquares

/-!
# Odd PSL₂ outer groups in field degree at most two

A diagonal automorphism squared is conjugation by the determinant-one matrix
`diag(u,u⁻¹)`. The existing semilinear calculation makes every outer square
diagonal in degrees one and two. Thus every outer element has fourth power
one. This supplies the literal odd PSL₂ source rows in A.3.8 without requiring
an additional full outer-group presentation. Source: GLS3, Theorem 2.5.12.
-/

public section
namespace Theory.PSL2.OuterSolvable.SmallDegreeSquares
open Matrix OddCoverage
variable {F : Type*} [Field F]

/-- Diagonal outer classes have square one over every field. -/
theorem diagonalOuter_square (u : Fˣ) : diagonalOuter u ^ 2 = 1 := by
  rw [← map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  refine ⟨torus u, ?_⟩
  apply MulEquiv.ext
  intro x
  obtain ⟨A, rfl⟩ := quotientMap_surjective F x
  rw [diagonalAutHom_apply_quotientMap]
  change quotientMap F (slTorus u * A * (slTorus u)⁻¹) =
    quotientMap F (slDiagonal (u ^ 2) A)
  apply congrArg (quotientMap F)
  apply Subtype.ext
  change (slTorus u).val * A.val * Matrix.adjugate (slTorus u).val = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [slTorus, slDiagonal, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.adjugate_fin_two, pow_two, mul_assoc, mul_comm]

/-- The full actual outer group in odd field degree one or two is a two-group. -/
theorem outer_isPGroup_two [Finite F] {p n : ℕ} (hp : p.Prime) (ho : Odd p)
    (hn : n ≤ 2) (hF : Nat.card F = p ^ n) : IsPGroup 2 (MulAut.Outer (Group F)) := by
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup (Group F)) x
  obtain ⟨u, hu⟩ := outer_square_mem hp ho hn hF a
  refine ⟨2, ?_⟩
  change (QuotientGroup.mk' (MulAut.innerSubgroup (Group F)) a) ^ (2 * 2) = 1
  rw [pow_mul, ← hu]
  exact diagonalOuter_square u

end Theory.PSL2.OuterSolvable.SmallDegreeSquares
