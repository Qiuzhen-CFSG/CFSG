module
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism.ShortTransport
public import Mathlib.Algebra.Polynomial.Coeff

/-!
# First coefficients of the concrete adjoint identity

Apply the proved adjoint equivariance over the polynomial ring and extract
the linear coefficient of a root parameter. This expresses every root-matrix
commutator as a linear combination of the fixed root and Cartan matrices.
The argument works in characteristic two and includes opposite roots.

Source: Steinberg (1963), §2, structure equations 2.1–2.6.
-/
public section
set_option backward.isDefEq.respectTransparency false
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open scoped Matrix
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity.RestrictedBridge.HighestLine.TriangularMatrices
open Geometry.ExceptionalMorphism
noncomputable section
universe u
variable {F : Type u} [Field F]
local notation "I" => F4Chevalley.BasisIndex

private def matrixCoeff (n : ℕ) (A : Matrix I I (Polynomial F)) : Matrix I I F :=
  fun i j => (A i j).coeff n

private theorem matrixCoeff_mul_one (A D : Matrix I I (Polynomial F)) :
    matrixCoeff 1 (A * D) = matrixCoeff 0 A * matrixCoeff 1 D +
      matrixCoeff 1 A * matrixCoeff 0 D := by
  ext i j
  simp only [matrixCoeff, Matrix.mul_apply, Matrix.add_apply,
    Polynomial.finsetSum_coeff, Polynomial.mul_coeff_one, Finset.sum_add_distrib]

private theorem coordinateOperator_C (j : I) :
    coordinateOperator (K := Polynomial F) j =
      (coordinateOperator (K := F) j).map Polynomial.C := by
  have cast_matrix (A : F4Chevalley.IntegralMatrix) :
      A.map (Int.castRingHom (Polynomial F)) =
        (A.map (Int.castRingHom F)).map Polynomial.C := by
    ext i j
    simp
  cases j with
  | inr r => exact cast_matrix _
  | inl i =>
    simp only [coordinateOperator, cast_matrix]
    change _ = Polynomial.C.mapMatrix _
    rw [map_sub, map_mul, map_mul]
    rfl

private theorem matrixCoeff_adjointMap (w : I → Polynomial F) (n : ℕ) :
    matrixCoeff n (adjointMap w) = adjointMap (fun j => (w j).coeff n) := by
  ext i j
  simp only [adjointMap, WordRelations.Faithfulness.Adjoint.linearExtension,
    LinearMap.coe_mk, AddHom.coe_mk, matrixCoeff, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Polynomial.finsetSum_coeff, coordinateOperator_C, Matrix.map_apply,
    Polynomial.coeff_mul_C]

private theorem matrixCoeff_rootCurve (r : F4Chevalley.Root) :
    matrixCoeff (F := F) 0 (F4Chevalley.rootCurve r Polynomial.X).val = 1 ∧
    matrixCoeff (F := F) 1 (F4Chevalley.rootCurve r Polynomial.X).val =
      coordinateOperator (K := F) (Sum.inr r) := by
  have cast_coeff (z : ℤ) (n : ℕ) :
      (z : Polynomial F).coeff n = (Polynomial.C (z : F)).coeff n := by
    rw [map_intCast]
  constructor <;> ext i j <;> by_cases hij : i = j <;>
    simp [matrixCoeff, F4Chevalley.rootCurve_matrix_formula, specializeMatrix,
      Matrix.one_apply, cast_coeff, hij,
      coordinateOperator, F4Chevalley.dividedPower_one, Polynomial.coeff_one]

/-- Every concrete root-matrix commutator is the adjoint image of a coordinate
vector. No root length, sign, or nonopposition restriction is imposed. -/
theorem root_commutator_eq_adjoint [CharP F 2] (r s : F4Chevalley.Root) :
    coordinateOperator (K := F) (Sum.inr r) * coordinateOperator (Sum.inr s) -
      coordinateOperator (Sum.inr s) * coordinateOperator (Sum.inr r) =
      adjointMap (coordinateOperator (K := F) (Sum.inr r) *ᵥ
        Pi.single (Sum.inr s) 1) := by
  classical
  let g := F4Chevalley.rootCurve r (Polynomial.X : Polynomial F)
  have hg : g ∈ matrixGroup (Polynomial F) := Subgroup.subset_closure ⟨(r, Polynomial.X), rfl⟩
  have h := adjointMap_equivariant g hg (Pi.single (Sum.inr s) 1)
  have he := congrArg (matrixCoeff (F := F) 1) h
  rw [matrixCoeff_mul_one, matrixCoeff_mul_one] at he
  have hcol (n : ℕ) :
      (fun j => ((g.val *ᵥ Pi.single (Sum.inr s) 1) j).coeff n) =
        matrixCoeff n g.val *ᵥ Pi.single (Sum.inr s) 1 := by
    ext j
    simp [matrixCoeff, Matrix.mulVec_single]
  rw [matrixCoeff_adjointMap, matrixCoeff_adjointMap, hcol, hcol,
    (matrixCoeff_rootCurve r).1, (matrixCoeff_rootCurve r).2,
    Matrix.one_mulVec, adjointMap_root_single] at he
  have hconst (n : ℕ) :
      matrixCoeff (F := F) n (adjointMap (Pi.single (Sum.inr s) 1)) =
        if n = 0 then coordinateOperator (K := F) (Sum.inr s) else 0 := by
    rw [adjointMap_single, coordinateOperator_C]
    ext i j
    by_cases hn : n = 0 <;> simp [matrixCoeff, Polynomial.coeff_C, hn]
  rw [hconst, hconst] at he
  simp only [ite_true, one_ne_zero, ite_false, mul_zero, zero_add, mul_one] at he
  change coordinateOperator (K := F) (Sum.inr s) * coordinateOperator (Sum.inr r) +
    adjointMap (coordinateOperator (K := F) (Sum.inr r) *ᵥ Pi.single (Sum.inr s) 1) =
    coordinateOperator (K := F) (Sum.inr r) * coordinateOperator (Sum.inr s) at he
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using he.symm)

end
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity.RestrictedBridge.HighestLine.TriangularMatrices
