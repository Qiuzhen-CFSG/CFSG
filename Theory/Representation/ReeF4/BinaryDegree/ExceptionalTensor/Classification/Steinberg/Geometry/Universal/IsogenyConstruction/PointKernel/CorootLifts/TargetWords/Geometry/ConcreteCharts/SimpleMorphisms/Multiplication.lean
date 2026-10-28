module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords.Geometry.ConcreteCharts.SimpleMorphisms.Polynomial
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords.Geometry.ConcreteCharts.SimpleMorphisms.Multiplication.CartanBlock
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords.Geometry.ConcreteCharts.SimpleMorphisms.Multiplication.StringAction

/-!
# Multiplicativity of the explicit simple-root F4 matrices

The Cartan columns and the two opposite-root columns satisfy multiplication by
the SL₂ determinant equations. Every remaining root belongs to an independent
root string, where multiplication is convolution of the integral divided-power
coefficients. Together these exhaust the Cartan-plus-root basis and prove the
matrix law without assuming an existing rank-one representation or any
comparison with elementary root curves.

Source: the integral construction underlying GLS3, Theorem 1.12.1 and
Remark 1.12.10. The polynomial candidate, including its Cartan coupling, is
exactly the one defined in `SimpleMorphisms.Polynomial`.
-/

@[expose] public section
noncomputable section
open scoped Matrix
open Theory.AlgebraicGroup.StandardRootSystem

namespace Theory.AlgebraicGroup.F4Chevalley.ConcreteCharts
open SimpleSL2Multiplication
local instance simpleSL2MultiplicationNeg : InvolutiveNeg Root := typeF4RootPairing.indexNeg
/-- The literal simple-root polynomial matrices give an SL₂ action in characteristic two. -/
theorem simpleSL2Matrix_mul {k : Type*} [Field k] [CharP k 2]
    (i : typeF4RootPairing_base.support) (A B : Matrix.SpecialLinearGroup (Fin 2) k) :
    simpleSL2Matrix i ((A * B : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      simpleSL2Matrix i (A : Matrix (Fin 2) (Fin 2) k) *
        simpleSL2Matrix i (B : Matrix (Fin 2) (Fin 2) k) := by
  classical
  have hcol (j : BasisIndex) :
      simpleSL2Matrix i ((A * B : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *ᵥ
          Pi.single j 1 =
        simpleSL2Matrix i (A : Matrix (Fin 2) (Fin 2) k) *ᵥ
          (simpleSL2Matrix i (B : Matrix (Fin 2) (Fin 2) k) *ᵥ Pi.single j 1) := by
    rcases j with j | j
    · exact cartan_column_mul i j A B
    · by_cases hp : j = (i : Root)
      · subst j
        exact positive_column_mul i A B
      by_cases hn : j = (-i : Root)
      · subst j
        exact negative_column_mul i A B
      exact independent_column_mul (independent_iff.mpr ⟨hp, hn⟩) _ _
  ext r j
  have h := hcol j
  rw [Matrix.mulVec_mulVec] at h
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using congrFun h r
end Theory.AlgebraicGroup.F4Chevalley.ConcreteCharts
