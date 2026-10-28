module

public import Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic.Diagonal
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The projective diagonal torus and its three-cycle

The coordinate cycle cannot be a scalar multiple of a diagonal matrix. It
therefore retains order three in PGL and its cyclic subgroup meets the actual
diagonal torus trivially. The normalization identity from `Diagonal` gives a
join of order `3 * |C|^3` for any odd-order norm-one parameter group C.
In particular, the extra factor three survives the literal scalar quotient.

This adapts the matrix-entry argument in the PSU₃
`OddCrossCharacteristic/ThreeTorus/Matrix/Index` module to the published PSU₄
maps. It supplies the local subgroup order for the covering-kernel input to
Aschbacher–Smith A.2.17, printed p.39, with I.1.1–I.1.4, printed pp.407–408.
-/

@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups PerfectCentralCovering
open Theory.SpecificGroups.ClassicalUnitary
namespace Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic
variable {F : Type*} [Field F]
variable (J : HermitianForm 4 F) (hJ : J.form = 1)
variable (C : Subgroup Fˣ) (hC : ∀ u : C, J.conj (u.val : F) * (u.val : F) = 1)

/-- Projectivization cannot identify the coordinate cycle with a diagonal matrix. -/
theorem cycle_not_mem_diagonal_range :
    cycle J hJ ∉ (diagonalProjective J hJ C hC).range := by
  rintro ⟨a, ha⟩
  have he : ProjGenLinGroup.mk (OddFourRanks.torusMatrix C a) =
      ProjGenLinGroup.mk (cycleGL (F := F)) := congrArg Subtype.val ha
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp he
  have h02 := congrArg (fun g : GL (Fin 4) F => g.val 0 2) hu
  simp [OddFourRanks.torusMatrix_val, GeneralLinearGroup.coe_scalar, Matrix.scalar,
    cycleGL] at h02

/-- The actual projective cycle has order three. -/
theorem cycle_orderOf : orderOf (cycle J hJ) = 3 := by
  apply orderOf_eq_prime (cycle_cube J hJ)
  intro he
  apply cycle_not_mem_diagonal_range J hJ (OddFourRanks.normOne J)
    (OddFourRanks.normOne_norm J)
  rw [he]
  exact one_mem _

/-- The diagonal torus and the cyclic supplement have trivial intersection. -/
theorem diagonal_range_disjoint_cycle [Finite F] :
    Disjoint (diagonalProjective J hJ C hC).range (zpowers (cycle J hJ)) := by
  classical
  rw [Subgroup.disjoint_def]
  intro x hx hy
  rw [mem_zpowers_iff_mem_range_orderOf, cycle_orderOf] at hy
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hy
  have hn3 : n < 3 := Finset.mem_range.mp hn
  interval_cases n
  · simp
  · simp only [pow_one] at hx
    exact (cycle_not_mem_diagonal_range J hJ C hC hx).elim
  · have h4 : (cycle J hJ ^ 2) ^ 2 = cycle J hJ := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_add, cycle_cube, pow_one, one_mul]
    exact (cycle_not_mem_diagonal_range J hJ C hC (h4 ▸ pow_mem hx 2)).elim

/-- The full odd-order diagonal torus gains a factor three from the coordinate cycle. -/
theorem diagonal_cycle_card [Finite F] (ho : (Nat.card C).Coprime 2) :
    Nat.card ((diagonalProjective J hJ C hC).range ⊔ zpowers (cycle J hJ) :
      Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) = Nat.card C ^ 3 * 3 := by
  rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
    (zpowers_le.mpr (threeCycle_mem_normalizer _ _ (cycle_diagonal J hJ C hC)))
    (diagonal_range_disjoint_cycle J hJ C hC), Nat.card_zpowers, cycle_orderOf]
  congr 1
  rw [← Nat.card_congr (MonoidHom.ofInjective
    (diagonalProjective_injective J hJ C hC ho)).toEquiv]
  simp [Nat.card_fun]

end Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic
