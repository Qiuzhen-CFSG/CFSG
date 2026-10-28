module

public import Theory.SpecificGroups.HaradaNorton.Simplicity.Center.FirstRow.Abstract
public import Theory.SpecificGroups.HaradaNorton.Simplicity.Center.FirstRow.AD
public import Theory.SpecificGroups.HaradaNorton.Simplicity.Center.FirstRow.BD
public import Theory.SpecificGroups.HaradaNorton.Simplicity.Center.FirstRow.X1
public import Theory.SpecificGroups.HaradaNorton.Simplicity.Center.FirstRow.X2
public import Theory.SpecificGroups.HaradaNorton.Simplicity.Center.FirstRow.X3
public import Theory.SpecificGroups.HaradaNorton.Simplicity.Center.FirstRow.X4
public import Theory.SpecificGroups.HaradaNorton.Simplicity.Center.FirstRow.X5
public import Theory.SpecificGroups.HaradaNorton.Simplicity.Center.FirstRow.X6
public import Theory.SpecificGroups.HaradaNorton.Simplicity.Center.FirstRow.X7
public import Theory.SpecificGroups.HaradaNorton.Simplicity.Center.FirstRow.X8

/-!
# First-row rigidity for the fixed Harada–Norton matrices

Set `W = BABBABBA` and `C = A - I + W(B - I)`. The singleton-row
path from 0 to 29 shows that row zero of C vanishes. The certified witness D
satisfies `CD = diag(0,1,…,1)`. Commuting with A and B implies commuting with C,
so row zero of `MCD = CMD` forces every off-diagonal entry of row zero of M
to vanish. The certificate uses only sparse left multiplication by A and B.

Source and attribution: `../../MatrixSources.md`. `FirstRow/Generate.py`
reproduces the witness tables and their kernel-checked product certificates.
-/

namespace HaradaNorton

set_option maxRecDepth 10000

private instance finAllDecidable (P : Fin 133 → Prop) [DecidablePred P] :
    Decidable (∀ i, P i) := @Nat.decidableForallFin 133 P inferInstance

private instance entriesDecidable (A B : Matrix133) :
    Decidable (∀ i j, A i j = B i j) :=
  @Nat.decidableForallFin 133 _ (fun i =>
    @Nat.decidableForallFin 133 _ (fun j => ZMod.decidableEq 5 (A i j) (B i j)))

open FirstRowCertificate

set_option maxHeartbeats 0 in
private theorem operator_row_zero : ∀ j, operator aMatrix bMatrix 0 j = 0 := by
  apply operator_zero_row aMatrix bMatrix <;> decide +kernel

set_option maxHeartbeats 0 in
private theorem initial_difference : BD - D = X0 := by
  have h : ∀ i j : Fin 133, (BD - D) i j = X0 i j := by decide +kernel
  exact Matrix.ext h

set_option maxHeartbeats 0 in
private theorem final_difference : AD - D + X8 =
    Matrix.diagonal (fun i : Fin 133 => if i = 0 then 0 else 1) := by
  have h : ∀ i j : Fin 133, (AD - D + X8) i j =
      Matrix.diagonal (fun k : Fin 133 => if k = 0 then 0 else 1) i j := by decide +kernel
  exact Matrix.ext h

private theorem operator_right_inverse : operator aMatrix bMatrix * D =
    Matrix.diagonal (fun i : Fin 133 => if i = 0 then 0 else 1) :=
  inverse_of_products aMatrix bMatrix D AD BD X0 X1 X2 X3 X4 X5 X6 X7 X8 _
    mul_AD mul_BD initial_difference mul_X1 mul_X2 mul_X3 mul_X4
    mul_X5 mul_X6 mul_X7 mul_X8 final_difference

/-- A matrix commuting with both fixed HN generators has scalar zeroth row. -/
public theorem commuting_matrix_row_zero
    (M : Matrix133) (ha : M * aMatrix = aMatrix * M)
    (hb : M * bMatrix = bMatrix * M) :
    ∀ j : Fin 133, M 0 j = if j = 0 then M 0 0 else 0 :=
  row_rigidity aMatrix bMatrix D operator_row_zero operator_right_inverse M ha hb

end HaradaNorton
