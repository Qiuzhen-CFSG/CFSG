module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm.FrameCertificate.StepRows

/-!
# Interpreting the checked Steps rows

The numerical row certificates are a separate cache boundary. This module
uses their proved equalities with the original packed matrix decoder.
Source: `Norm/source/README.md` and the unchanged constants in `Norm.Frame`.
-/

public section
open Matrix
open Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration
open FactorAlgebras.Certificate MatrixChecks
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm

set_option maxRecDepth 8192 in
private theorem step_indices : ∀ (s : Fin 11) (t : Fin 22),
    entry FrameCertificate.stepInputs (22 * s.val + t.val) = entry orbitRows (23 * s.val + t.val) ∧
    entry FrameCertificate.stepOutputs (22 * s.val + t.val) = entry orbitRows (23 * s.val + (t.val + 1)) :=
  by decide +kernel

/-- Each of the eleven chains follows the literal right-row action. -/
theorem frame_steps (s : Fin 11) (t : Fin 22) :
    Matrix.vecMul (orbitRow s t.val) generatorProduct = orbitRow s (t.val + 1) := by
  have h := product_rows FrameCertificate.stepInputs c3 FrameCertificate.stepOutputs (n := 242) (by decide +kernel)
    FrameCertificate.step_rows ⟨22 * s.val + t.val, by omega⟩
  change combineList c3 (entry FrameCertificate.stepInputs (22 * s.val + t.val)) =
    entry FrameCertificate.stepOutputs (22 * s.val + t.val) at h
  rw [(step_indices s t).1, (step_indices s t).2] at h
  exact (vector_combine c3 (by decide +kernel) _).symm.trans (congrArg vector h)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm
