module

public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Structure.ProjectiveTorus

/-!
# A signed transposition in every unitary-three frame

The negative of the permutation interchanging coordinates zero and one has
square one and determinant one in dimension three, in every characteristic.
It preserves the identity Gram matrix and interchanges diag(a,b,(ab)⁻¹) and
diag(b,a,(ab)⁻¹). Conjugating by the actual orthonormal basis transports this
identity to an arbitrary Hermitian form, and the literal specialToProjective
map gives the required projective conjugation equation.

Source: the split-torus calculation underlying Aschbacher–Smith I.1.3(2)
and I.1.4(2), printed pp.407–408 (PDF pp.418–419), and GLS3 §6.1.
The frame coordinates are the existing UnitaryThree.OddTorusNormalizer API.
-/

public section

open Matrix Subgroup BenderSuzuki.MatrixGroups
open HermitianForm HermitianForm.IdentityGram HermitianForm.EvenInner
open UnitaryThree.OddTorusNormalizer

namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.OddCrossCharacteristic.SplitTorus
variable {F : Type*} [Field F]

/-- The negative of the transposition of the first two coordinates. -/
@[expose] def signedSwapGL : GL (Fin 3) F where
  val := !![0, -1, 0; -1, 0, 0; 0, 0, -1]
  inv := !![0, -1, 0; -1, 0, 0; 0, 0, -1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

/-- The signed permutation preserves the identity form and has determinant one. -/
theorem signedSwapGL_special (J : HermitianForm 3 F) :
    signedSwapGL ∈ (identityGram J).specialSubgroup := by
  rw [mem_specialSubgroup_iff]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [HermitianForm.conjTranspose, signedSwapGL, identityGram_form,
        Matrix.mul_apply, Fin.sum_univ_three]
  · apply Units.ext
    change (signedSwapGL (F := F)).val.det = 1
    simp [signedSwapGL, Matrix.det_fin_three]

/-- The signed permutation in the original orthonormal frame. -/
@[expose] def signedSwap (J : HermitianForm 3 F) (P : OrthogonalFrame J) : J.specialSubgroup :=
  (specialEquiv J P.val P.property).symm ⟨signedSwapGL, signedSwapGL_special J⟩

private theorem signedSwap_val (J : HermitianForm 3 F) (P : OrthogonalFrame J) :
    (signedSwap J P).val = P.val * signedSwapGL * P.val⁻¹ :=
  specialEquiv_symm_apply J P.val P.property _

/-- Conjugation interchanges the two independent norm-one coordinates. -/
theorem signedSwap_pair (J : HermitianForm 3 F) (P : OrthogonalFrame J)
    (a b : normOne J) :
    signedSwap J P * specialPairHom J P (a,b) * (signedSwap J P)⁻¹ =
      specialPairHom J P (b,a) := by
  apply Subtype.ext
  change (signedSwap J P).val * (specialPairHom J P (a,b)).val *
    (signedSwap J P).val⁻¹ = (specialPairHom J P (b,a)).val
  rw [signedSwap_val]
  change (MulAut.conj P.val) signedSwapGL *
      (MulAut.conj P.val) (diagonalHom (pairDiagonal J (a,b))) *
      ((MulAut.conj P.val) signedSwapGL)⁻¹ =
    (MulAut.conj P.val) (diagonalHom (pairDiagonal J (b,a)))
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [signedSwapGL, diagonalHom, pairDiagonal,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, mul_comm]

/-- The swapping equation descends through the literal special-to-projective map. -/
theorem projective_signedSwap_pair (J : HermitianForm 3 F) (P : OrthogonalFrame J)
    (a b : normOne J) :
    J.specialToProjective (signedSwap J P) * projectivePairHom J P (a,b) *
        (J.specialToProjective (signedSwap J P))⁻¹ = projectivePairHom J P (b,a) := by
  simpa only [projectivePairHom, MonoidHom.comp_apply, map_mul, map_inv] using
    congrArg J.specialToProjective (signedSwap_pair J P a b)

end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.OddCrossCharacteristic.SplitTorus
