module
public import Theory.AlgebraicGroup.RootSystems.F4WeightAction.Stabilizer.Rows

/-! Complete arithmetic certificate for the actual integral F4 Weyl action.
The 1,152-element census is checked in bounded rows. The sixteen exceptional
matrices are retained, and four explicit cubic-line factorizations handle their
point-dependent stabilizers. No classification result is assumed here. -/
public noncomputable section
namespace Theory.AlgebraicGroup.StandardRootSystem.F4WeightAction.Stabilizer.Checks
open Data Verifier

theorem certificate : Certificate where
  words_zero := by decide +kernel
  matrix_zero := by decide +kernel
  parent_spec k hk := parentOK_sound (rows_sound Rows.checked k).1 hk
  next_columns k i j := nextOK_sound (rows_sound Rows.checked k).2.1 i j
  root_coordinates := by decide +kernel
  reflection_matrix := by decide +kernel
  ordinary_path k hk := by
    have h := (rows_sound Rows.checked k).2.2.1
    rw [branchOK, hk] at h
    exact pathOK_sound h
  ordinary_witness k x hx := by
    have h := (rows_sound Rows.checked k).2.2.2
    exact vectorOK_sound ((List.all_eq_true.mp h) x hx)
  exception_index k j hk := by
    have h := (rows_sound Rows.checked k).2.2.1
    simpa only [branchOK, hk, beq_iff_eq] using h
  exception_conjugate := by decide +kernel
  cube := by decide +kernel
  lines := by decide +kernel
  exceptional_path := by decide +kernel
  exceptional_witness := by decide +kernel

end Theory.AlgebraicGroup.StandardRootSystem.F4WeightAction.Stabilizer.Checks
