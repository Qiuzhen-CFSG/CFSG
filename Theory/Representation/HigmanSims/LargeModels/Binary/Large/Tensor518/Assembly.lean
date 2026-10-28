module
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Ambient
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Data
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Pivot

/-!
# Tensor-section certificates supply the marked degree-518 HS action

The actual tensor representation is restricted to the annihilator of the 21
kernel rows. Multiplication by the 518 lift rows then realizes its quotient in
the published coordinates. The pivot-minor inverse makes this map surjective.
The four generator identities and minor inverse remain explicit numerical
obligations; no full degree-518 construction is asserted before they are proved.

Source: ATLAS HSG1-f2r518B0 and the section data in `Binary/source/README.md`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Tensor518
open Sporadic.LeechRelated.HS

/-- The literal shared first generator, with its concrete dimension exposed to
rectangular matrix multiplication. This changes no entry or basis. -/
def targetA : Matrix (Fin 518) (Fin 518) (ZMod 2) := aMatrix 2

/-- The literal shared second generator in the same concrete coordinate type. -/
def targetB : Matrix (Fin 518) (Fin 518) (ZMod 2) := bMatrix 2

theorem targetA_eq : targetA = aMatrix 2 := rfl
theorem targetB_eq : targetB = bMatrix 2 := rfl

/-- The literal pivot-minor calculation supplies a right inverse to the stacked
rows in the exact sum-index convention of `Descent`. -/
theorem stacked_rightInverse_of_pivotInverse
    (h : pivotMinor * pivotInverse = 1) :
    ∃ R : Matrix (Fin 1120) (Fin 21 ⊕ Fin 518) (ZMod 2),
      Descent.stackedRows kernelMatrix liftMatrix * R = 1 := by
  apply rightInverse_of_pivotMinor kernelMatrix liftMatrix pivotColumn pivotInverse
  exact h

/-- The supplied minor inverse implies surjectivity from the annihilator of N. -/
theorem rowSurjectivity_of_pivotInverse (h : pivotMinor * pivotInverse = 1) :
    ∀ y : Fin 518 → ZMod 2, ∃ x,
      kernelMatrix.mulVec x = 0 ∧ liftMatrix.mulVec x = y := by
  obtain ⟨R, hR⟩ := stacked_rightInverse_of_pivotInverse h
  exact Descent.rowSubquotient_surjective_of_rightInverse kernelMatrix liftMatrix R hR

/-- Application to the actual tensor action and exact shared target matrices.
Only the four numerical intertwining identities and pivot-minor inverse remain
in addition to the two input actions. This is not yet the completed degree-518
construction: its assembly owner must discharge these numerical premises. -/
theorem markedAction_of_certificates
    (h20 : Nonempty Twenty.MarkedComparison) (C56 : MarkedAction 0)
    (hNa : kernelMatrix * ambientA = aKernelMatrix * kernelMatrix)
    (hNb : kernelMatrix * ambientB = bKernelMatrix * kernelMatrix)
    (hUa : liftMatrix * ambientA = aCorrectionMatrix * kernelMatrix + targetA * liftMatrix)
    (hUb : liftMatrix * ambientB = bCorrectionMatrix * kernelMatrix + targetB * liftMatrix)
    (hR : pivotMinor * pivotInverse = 1) : Nonempty (MarkedAction 2) := by
  obtain ⟨C20⟩ := h20
  apply Descent.markedAction_of_rowSubquotient 2 1120 21 (ambientAction C20 C56)
    kernelMatrix liftMatrix aKernelMatrix bKernelMatrix aCorrectionMatrix bCorrectionMatrix
  · rw [ambientAction_matrix_a]
    exact hNa
  · rw [ambientAction_matrix_b]
    exact hNb
  · rw [ambientAction_matrix_a]
    exact hUa
  · rw [ambientAction_matrix_b]
    exact hUb
  · exact rowSurjectivity_of_pivotInverse hR

end Representation.HigmanSims.LargeModels.Binary.Large.Tensor518
