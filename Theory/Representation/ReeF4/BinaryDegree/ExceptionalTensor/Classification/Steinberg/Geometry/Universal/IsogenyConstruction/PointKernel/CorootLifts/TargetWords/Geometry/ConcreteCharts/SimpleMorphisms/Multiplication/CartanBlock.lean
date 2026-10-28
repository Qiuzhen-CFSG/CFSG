module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords.Geometry.ConcreteCharts.SimpleMorphisms.Polynomial

/-!
# Multiplication on the Cartan and opposite-root columns

The opposite roots form the quadratic rank-one block, and every Cartan column
couples to this block through the literal absolute Cartan coefficient. Expanding
these three kinds of columns gives the multiplication law from the two SL₂
determinant equations. Characteristic two fixes the distinguished Cartan vector;
the remaining Cartan coupling terms are retained throughout.
Source: the integral construction underlying GLS3, 1.12.1 and Remark 1.12.10.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open Theory.AlgebraicGroup.StandardRootSystem
open scoped Matrix
namespace Theory.AlgebraicGroup.F4Chevalley.ConcreteCharts.SimpleSL2Multiplication
local instance cartanBlockNeg : InvolutiveNeg Root := typeF4RootPairing.indexNeg

variable {k : Type*} [Field k]
/-- A Cartan basis column over the coefficient field. -/
abbrev cartanVector (j : typeF4RootPairing_base.support) : BasisIndex → k := Pi.single (Sum.inl j) 1
/-- A root basis column over the coefficient field. -/
abbrev rootVector (j : Root) : BasisIndex → k := Pi.single (Sum.inr j) 1
/-- The integral Cartan coupling specialized to the coefficient field. -/
abbrev cartanCoefficient (i j : typeF4RootPairing_base.support) : k := (|typeF4RootPairing_base.cartanMatrix i j| : ℤ)

lemma cartan_column (i j : typeF4RootPairing_base.support) (A : Matrix (Fin 2) (Fin 2) k) :
    simpleSL2Matrix i A *ᵥ cartanVector j =
      cartanVector j + (cartanCoefficient i j * A 0 1 * A 1 0) • cartanVector i +
        (cartanCoefficient i j * A 0 0 * A 0 1) • rootVector (i : Root) +
          (cartanCoefficient i j * A 1 0 * A 1 1) • rootVector (-i : Root) := by
  classical
  ext (r | r) <;>
    simp [simpleSL2Matrix, cartanVector, rootVector, cartanCoefficient, Pi.single_apply, eq_comm]

lemma positive_column (i : typeF4RootPairing_base.support) (A : Matrix (Fin 2) (Fin 2) k) :
    simpleSL2Matrix i A *ᵥ rootVector (i : Root) =
      (A 0 0 * A 1 0) • cartanVector i + (A 0 0 ^ 2) • rootVector (i : Root) +
        (A 1 0 ^ 2) • rootVector (-i : Root) := by
  classical
  have hn : (i : Root) ≠ typeF4RootPairing.reflectionPerm i i := typeF4RootPairing.ne_neg i
  ext (r | r) <;>
    simp [simpleSL2Matrix, cartanVector, rootVector, Pi.single_apply, eq_comm, hn]

lemma negative_column (i : typeF4RootPairing_base.support) (A : Matrix (Fin 2) (Fin 2) k) :
    simpleSL2Matrix i A *ᵥ rootVector (-i : Root) =
      (A 0 1 * A 1 1) • cartanVector i + (A 0 1 ^ 2) • rootVector (i : Root) +
        (A 1 1 ^ 2) • rootVector (-i : Root) := by
  classical
  have hn : (i : Root) ≠ typeF4RootPairing.reflectionPerm i i := typeF4RootPairing.ne_neg i
  ext (r | r) <;>
    simp [simpleSL2Matrix, cartanVector, rootVector, Pi.single_apply, eq_comm, hn]

variable [CharP k 2]

lemma fixed_cartan (i : typeF4RootPairing_base.support) (A : Matrix (Fin 2) (Fin 2) k) :
    simpleSL2Matrix i A *ᵥ cartanVector i = cartanVector i := by
  rw [cartan_column]
  have hc : cartanCoefficient (k := k) i i = 0 := by
    norm_num [cartanCoefficient]
    exact CharP.cast_eq_zero k 2
  simp [hc]

lemma sl2_det (A : Matrix.SpecialLinearGroup (Fin 2) k) :
    A 0 0 * A 1 1 + A 0 1 * A 1 0 = 1 := by
  simpa only [Matrix.det_fin_two, CharTwo.sub_eq_add] using A.det_coe

lemma positive_column_mul (i : typeF4RootPairing_base.support) (A B : Matrix.SpecialLinearGroup (Fin 2) k) :
    simpleSL2Matrix i (↑(A * B) : Matrix (Fin 2) (Fin 2) k) *ᵥ rootVector (i : Root) =
      simpleSL2Matrix i (A : Matrix (Fin 2) (Fin 2) k) *ᵥ
        (simpleSL2Matrix i (B : Matrix (Fin 2) (Fin 2) k) *ᵥ rootVector (i : Root)) := by
  rw [positive_column, positive_column]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, fixed_cartan, positive_column, negative_column]
  ext x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_sq, mul_pow]
  linear_combination (B 0 0 * B 1 0 * cartanVector (k := k) i x) * sl2_det A

lemma negative_column_mul (i : typeF4RootPairing_base.support) (A B : Matrix.SpecialLinearGroup (Fin 2) k) :
    simpleSL2Matrix i (↑(A * B) : Matrix (Fin 2) (Fin 2) k) *ᵥ rootVector (-i : Root) =
      simpleSL2Matrix i (A : Matrix (Fin 2) (Fin 2) k) *ᵥ
        (simpleSL2Matrix i (B : Matrix (Fin 2) (Fin 2) k) *ᵥ rootVector (-i : Root)) := by
  rw [negative_column, negative_column]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, fixed_cartan, positive_column, negative_column]
  ext x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_sq, mul_pow]
  linear_combination (B 0 1 * B 1 1 * cartanVector (k := k) i x) * sl2_det A

lemma cartan_column_mul (i j : typeF4RootPairing_base.support) (A B : Matrix.SpecialLinearGroup (Fin 2) k) :
    simpleSL2Matrix i (↑(A * B) : Matrix (Fin 2) (Fin 2) k) *ᵥ cartanVector j =
      simpleSL2Matrix i (A : Matrix (Fin 2) (Fin 2) k) *ᵥ
        (simpleSL2Matrix i (B : Matrix (Fin 2) (Fin 2) k) *ᵥ cartanVector j) := by
  rw [cartan_column, cartan_column]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, fixed_cartan, cartan_column,
    positive_column, negative_column]
  ext x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply, Fin.sum_univ_two]
  have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
  linear_combination
    (cartanCoefficient i j * B 0 1 * B 1 0 * cartanVector (k := k) i x) * sl2_det A +
    (cartanCoefficient i j * (A 0 1 * A 1 0 * cartanVector (k := k) i x +
      A 0 0 * A 0 1 * rootVector (k := k) (i : Root) x +
      A 1 0 * A 1 1 * rootVector (k := k) (-i : Root) x)) * sl2_det B -
    (cartanCoefficient i j * A 0 1 * A 1 0 * B 0 1 * B 1 0 * cartanVector (k := k) i x) * htwo

end Theory.AlgebraicGroup.F4Chevalley.ConcreteCharts.SimpleSL2Multiplication
