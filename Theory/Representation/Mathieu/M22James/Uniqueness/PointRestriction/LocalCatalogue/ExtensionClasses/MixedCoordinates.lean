module

public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue.ExtensionClasses.Reduction

/-!
# Two explicit cross-block formulas for the mixed SL₃(4) calculation

The first matrix has entries `(g[i,j+1] * g[i,j+2])²`, with cyclic indices
modulo three. It is the cross term suggested by the symmetric square, after
identifying its squared-coordinate submodule with the binary natural module.
The second formula is the squared transpose of the first evaluated at `g⁻¹`,
as suggested by binary duality. Both act on vectors after coordinatewise
Frobenius. Their linear combination has two explicit parameters in F₄.

For `x_ij(t)` and the remaining index k, the action of the cross block is
`p e_i t² v_k² + q e_k t v_i²`. The root family is proved to generate SL₃(4)
in `Reduction`. This module proves binary linearity, the displayed root
formulas, and vanishing at one and the central scalar. The full cocycle laws,
nonsplitting, and exhaustive coverage are separate obligations; these formulas
alone are not asserted to be representations or a classification.

Source context: the natural-by-dual point restriction in Aschbacher–Smith,
H.12.1, printed p.394, following James (1973), Lemma 8.3. The coordinate
formulas are the elementary symmetric-square and dual constructions.
-/

@[expose] public noncomputable section

namespace Representation.SL3FourLocalCatalogue
namespace ExtensionCoordinates

/-- Coordinatewise Frobenius on the actual binary three-coordinate space. -/
def squareVector : W ≃ₗ[ZMod 2] W where
  toFun v i := SL2FourNatural.fieldFrobenius (v i)
  invFun v i := SL2FourNatural.fieldFrobenius (v i)
  left_inv v := by funext i; exact SL2FourNatural.fieldFrobenius_involutive _
  right_inv v := by funext i; exact SL2FourNatural.fieldFrobenius_involutive _
  map_add' v w := by funext i; exact map_add SL2FourNatural.fieldFrobenius _ _
  map_smul' c v := by
    funext i
    change SL2FourNatural.fieldFrobenius (c • v i) = c • SL2FourNatural.fieldFrobenius (v i)
    fin_cases c
    · change SL2FourNatural.fieldFrobenius ((0 : ZMod 2) • v i) =
        (0 : ZMod 2) • SL2FourNatural.fieldFrobenius (v i)
      simp
    · change SL2FourNatural.fieldFrobenius ((1 : ZMod 2) • v i) =
        (1 : ZMod 2) • SL2FourNatural.fieldFrobenius (v i)
      simp

/-- A matrix applied after coordinatewise squaring, regarded as a binary linear map. -/
def matrixSemilinear (M : Matrix (Fin 3) (Fin 3) F) : W →ₗ[ZMod 2] W :=
  (M.mulVecLin.restrictScalars (ZMod 2)).comp squareVector.toLinearMap

/-- The Frobenius coordinate formula. -/
lemma squareVector_apply (v : W) (i : Fin 3) : squareVector v i = (v i)^2 := rfl

/-- Frobenius conjugates the ordinary field scalars. -/
lemma squareVector_smul (r : F) (v : W) : squareVector (r • v) = r^2 • squareVector v := by
  funext i
  exact map_mul SL2FourNatural.fieldFrobenius r (v i)

/-- The explicit matrix formula on every vector. -/
lemma matrixSemilinear_apply (M : Matrix (Fin 3) (Fin 3) F) (v : W) (i : Fin 3) :
    matrixSemilinear M v i = ∑ j, M i j * (v j)^2 := rfl

/-- The cross-block matrix construction is Frobenius-semilinear over the ordinary field. -/
lemma matrixSemilinear_smul (M : Matrix (Fin 3) (Fin 3) F) (r : F) (v : W) :
    matrixSemilinear M (r • v) = r^2 • matrixSemilinear M v := by
  change M.mulVecLin (squareVector (r • v)) = r^2 • M.mulVecLin (squareVector v)
  rw [squareVector_smul, map_smul]

/-- Distinct coefficient matrices give distinct binary linear maps. -/
lemma matrixSemilinear_injective : Function.Injective matrixSemilinear := by
  intro M N h
  apply Matrix.ext_of_mulVec_single
  intro j
  have hv := LinearMap.congr_fun h (squareVector.symm (Pi.single j 1))
  change M.mulVec (squareVector (squareVector.symm (Pi.single j 1))) =
    N.mulVec (squareVector (squareVector.symm (Pi.single j 1))) at hv
  simpa only [LinearEquiv.apply_symm_apply] using hv

/-- The squared row-product matrix of cross terms. -/
def symmetricMatrix (g : SL) : Matrix (Fin 3) (Fin 3) F :=
  fun i j => (g i (j + 1) * g i (j + 2)) ^ 2

/-- The binary-dual cross term, including the inverse group element. -/
def dualSymmetricMatrix (g : SL) : Matrix (Fin 3) (Fin 3) F :=
  fun i j => (symmetricMatrix g⁻¹ j i) ^ 2

/-- The proposed mixed cross block with two independent field coefficients. -/
def mixedValue (p q : F) (g : SL) : W →ₗ[ZMod 2] W :=
  matrixSemilinear (p • symmetricMatrix g + q • dualSymmetricMatrix g)

/-- The complete vector formula for the proposed mixed cross block. -/
lemma mixedValue_apply (p q : F) (g : SL) (v : W) (i : Fin 3) :
    mixedValue p q g v i = ∑ j,
      (p * symmetricMatrix g i j + q * dualSymmetricMatrix g i j) * (v j)^2 := rfl

/-- The first cross-term matrix vanishes at the identity. -/
lemma symmetricMatrix_one : symmetricMatrix 1 = 0 := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [symmetricMatrix]

/-- The second cross-term matrix vanishes at the identity. -/
lemma dualSymmetricMatrix_one : dualSymmetricMatrix 1 = 0 := by
  funext i j
  simp [dualSymmetricMatrix, symmetricMatrix_one]

/-- The first cross-term matrix vanishes at the central scalar. -/
lemma symmetricMatrix_z : symmetricMatrix z = 0 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [symmetricMatrix, z, SL3FourNaturalDual.centralScalar]

/-- The second cross-term matrix vanishes at the central scalar. -/
lemma dualSymmetricMatrix_z : dualSymmetricMatrix z = 0 := by
  have hi : z⁻¹ = z ^ 2 := by
    apply inv_eq_of_mul_eq_one_left
    decide +kernel
  have hp : symmetricMatrix (z ^ 2) = 0 := by
    funext i j
    change (((z ^ 2).val i (j + 1) * (z ^ 2).val i (j + 2)) ^ 2) = 0
    rw [Matrix.SpecialLinearGroup.coe_pow]
    fin_cases i <;> fin_cases j <;>
      simp [z, SL3FourNaturalDual.centralScalar, Matrix.diagonal_pow]
  funext i j
  simp only [dualSymmetricMatrix, hi, hp, Matrix.zero_apply, zero_pow, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true]

/-- Every proposed linear combination has the required value at one. -/
lemma mixedValue_one (p q : F) : mixedValue p q 1 = 0 := by
  apply LinearMap.ext
  intro v
  funext i
  simp [mixedValue_apply, symmetricMatrix_one, dualSymmetricMatrix_one]

/-- Every proposed linear combination is normalized at the central scalar. -/
lemma mixedValue_z (p q : F) : mixedValue p q z = 0 := by
  apply LinearMap.ext
  intro v
  funext i
  simp [mixedValue_apply, symmetricMatrix_z, dualSymmetricMatrix_z]

/-- The first coefficient matrix on each elementary transvection. -/
lemma symmetricMatrix_transvection {i j k : Fin 3} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (t : F) :
    symmetricMatrix (Matrix.SpecialLinearGroup.transvection hij t) = Matrix.single i k (t^2) := by
  funext r s
  fin_cases i <;> fin_cases j <;> try exact (hij rfl).elim
  all_goals fin_cases k <;> try exact (hik rfl).elim
  all_goals try exact (hjk rfl).elim
  all_goals fin_cases r <;> fin_cases s <;>
    simp [symmetricMatrix, Matrix.SpecialLinearGroup.transvection_coe]

/-- The second coefficient matrix on each elementary transvection. -/
lemma dualSymmetricMatrix_transvection {i j k : Fin 3} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (t : F) :
    dualSymmetricMatrix (Matrix.SpecialLinearGroup.transvection hij t) = Matrix.single k i t := by
  funext r s
  change (symmetricMatrix ((Matrix.SpecialLinearGroup.transvection hij t)⁻¹) s r)^2 = _
  rw [Matrix.SpecialLinearGroup.transvection_inv, symmetricMatrix_transvection hij hik hjk]
  by_cases hr : r = k <;> by_cases hs : s = i <;>
    simp [Matrix.single_apply, hr, hs, eq_comm, and_comm, ← pow_mul, SL2FourNatural.pow_four]

/-- The two-parameter action formula on the proved generating family. -/
lemma mixedValue_transvection {i j k : Fin 3} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (p q t : F) (v : W) :
    mixedValue p q (Matrix.SpecialLinearGroup.transvection hij t) v =
      p • Pi.single i (t^2 * (v k)^2) + q • Pi.single k (t * (v i)^2) := by
  change (p • symmetricMatrix _ + q • dualSymmetricMatrix _).mulVec _ = _
  rw [symmetricMatrix_transvection hij hik hjk, dualSymmetricMatrix_transvection hij hik hjk,
    Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.single_mulVec_eq, Matrix.single_mulVec_eq]
  simp only [← Pi.single_smul, smul_eq_mul, mul_one]
  rfl

end ExtensionCoordinates
end Representation.SL3FourLocalCatalogue
