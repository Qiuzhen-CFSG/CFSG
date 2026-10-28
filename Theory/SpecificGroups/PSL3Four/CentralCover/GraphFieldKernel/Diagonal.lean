module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.CoverCentralizers.CoverAction.DiagonalCenter.KernelGeneration
public import Theory.SpecificGroups.PSL3.OuterSolvable.StandardQuotient
/-!
# The actual graph-field and diagonal automorphisms commute

Inverse transpose composed with Frobenius fixes the one-coordinate diagonal
conjugating matrix over the four-element field. Its induced projective action
therefore commutes with graph-field. The proved concrete exceptional-cover
calculation supplies a diagonal actor moving a nonsquare kernel class; no
outer action or multiplier compatibility is assumed.

Source: Aschbacher–Smith I.2.2(3b), printed pp.409–410, and I.1.3(6), p.407.
-/

public section
open PerfectCentralCovering Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3Four.CentralCover.GraphFieldKernel
open ExtendedCentralizer.CoverCentralizers.DiagonalCenter
open Matrix.PSL3.OuterSolvable
open ExtendedCentralizer.ProjectiveFixer

private theorem determinantDiagonal_graphField (u : Fˣ) :
    inverseTransposeGL F (GeneralLinearGroup.map fieldFrobenius.toRingHom
      (determinantDiagonal u))=determinantDiagonal u := by
  apply Units.ext
  ext i j
  change fieldFrobenius ((Matrix.diagonal
    (fun i => ((![u,1,1] i)⁻¹ : Fˣ).val)) j i) =
    Matrix.diagonal (fun i => ((![u,1,1] i) : Fˣ).val) i j
  have hu : fieldFrobenius (u⁻¹ : Fˣ) = (u : F) := by
    change (↑u⁻¹ : F)^2=(u : F)
    rw [unit_inv]
    simpa only [Units.val_pow_eq_pow_val,←pow_mul] using pow_four (u : F)
  fin_cases i <;> fin_cases j <;> simp
  simpa using hu

theorem graphField_commutes_diagonal (u : Fˣ) :
    Commute graphField (diagonalRepresentative u) := by
  change (graph F*pslFrobenius)*linearConj F (determinantDiagonal u)=
    linearConj F (determinantDiagonal u)*(graph F*pslFrobenius)
  rw [frobenius_eq_fieldAction,mul_assoc,field_linearConj,←mul_assoc,
    graph_linearConj,determinantDiagonal_graphField,mul_assoc]

theorem diagonalRepresentative_cube (u : Fˣ) : diagonalRepresentative u ^3=1 := by
  have hdiag : determinantDiagonal u ^3=1 := by
    apply Units.ext
    change (Matrix.diagonal (fun i => ((![u,1,1] i) : Fˣ).val))^3=1
    rw [Matrix.diagonal_pow]
    have hu : (u : F)^3=1 := by
      simpa only [Units.val_pow_eq_pow_val,Units.val_one] using congrArg Units.val (unit_cube u)
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    exact hu
  change linearConj F (determinantDiagonal u)^3=1
  rw [←map_pow,hdiag,map_one]

theorem exists_moving_diagonal : ∃ u : Fˣ, ∃ z : (universalProjection PSL).ker,
      ¬ ∃ w, w^2=universalKernelMap (diagonalRepresentative u) z*z⁻¹ := by
  obtain ⟨z,hz⟩ := universal_actor_moves_modulo_squares
  obtain ⟨g,hg⟩ := linearConj_eq_diagonal_mul_inner diagonalOverCanonical
  rw [←actor_eq_linear] at hg
  refine ⟨GeneralLinearGroup.det diagonalOverCanonical,z,?_⟩
  have he : universalKernelMap PSL3.ExceptionalFourCover.KernelModel.DiagonalWords.actor z =
    universalKernelMap (diagonalRepresentative (GeneralLinearGroup.det diagonalOverCanonical)) z := by
    apply Subtype.ext
    change universalLift PSL3.ExceptionalFourCover.KernelModel.DiagonalWords.actor z =
      universalLift (diagonalRepresentative (GeneralLinearGroup.det diagonalOverCanonical)) z
    rw [hg,universalLift_mul_inner_apply]
  rwa [he] at hz
end Matrix.PSL3Four.CentralCover.GraphFieldKernel
