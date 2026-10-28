module

public import Theory.AtlasPort.Algebra.SplitOctonion.Automorphism

/-!
# Norm geometry of the split octonions

The polar form of the octonion norm is nondegenerate. Right multiplication
by a vector of nonzero norm is an invertible linear map: its inverse is
right multiplication by the conjugate, divided by the norm. The inverse
identities are proved from the multiplication table, without assuming
associativity of the octonions.

These facts support the eigenspace geometry of elementary two-groups.
Coordinate conventions: the licensed ATLAS split-octonion port, Wilson's
integral table, Eq. (4.11); see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

namespace Atlas.SplitOctonion
variable {F : Type*} [Field F]

/-- The polar bilinear form of the split norm. -/
def normPolar : Carrier F →ₗ[F] Carrier F →ₗ[F] F where
  toFun x :=
    { toFun := fun y =>
        x 0*y 7 + x 7*y 0 + x 1*y 6 + x 6*y 1 +
          x 2*y 5 + x 5*y 2 + x 3*y 4 + x 4*y 3
      map_add' y z := by simp; ring
      map_smul' r y := by simp; ring }
  map_add' x y := by ext z; simp; ring
  map_smul' r x := by ext z; simp; ring

theorem norm_smul (r : F) (x : Carrier F) : norm (r • x) = r^2 * norm x := by
  simp [norm]; ring

theorem norm_add (x y : Carrier F) :
    norm (x + y) = norm x + norm y + normPolar x y := by
  simp [norm, normPolar]; ring

theorem normPolar_self (x : Carrier F) : normPolar x x = 2 * norm x := by
  simp [norm, normPolar]; ring

theorem normPolar_symm (x y : Carrier F) : normPolar x y = normPolar y x := by
  simp [normPolar]; ring

theorem normPolar_eq (x y : Carrier F) :
    normPolar x y = norm (x+y) - norm x - norm y := by
  rw [norm_add]; ring

theorem normPolar_nondegenerate {x : Carrier F}
    (h : ∀ y, normPolar x y = 0) : x = 0 := by
  funext i
  have hi := h (basisVector (7-i))
  fin_cases i <;> simpa [normPolar, basisVector] using hi

@[simp] theorem automorphism_normPolar (g : Automorphism F) (x y : Carrier F) :
    normPolar (g.val x) (g.val y) = normPolar x y := by
  simp only [normPolar_eq, ← map_add, automorphism_norm]

theorem conjugate_smul (r : F) (x : Carrier F) :
    conjugate (r • x) = r • conjugate x := by
  ext i; fin_cases i <;> simp [conjugate, trace, unit, Matrix.vecHead, Matrix.vecTail]

/-- The right inverse identity needed for division by a nonisotropic vector. -/
theorem mul_mul_conjugate_right (x v : Carrier F) :
    mul (mul x v) (conjugate v) = norm v • x := by
  ext i; fin_cases i <;> simp [mul, conjugate, trace, norm, unit] <;> ring

/-- The reverse right inverse identity, also valid at isotropic vectors. -/
theorem mul_conjugate_mul_right (x v : Carrier F) :
    mul (mul x (conjugate v)) v = norm v • x := by
  ext i; fin_cases i <;> simp [mul, conjugate, trace, norm, unit] <;> ring

/-- Right multiplication by a vector with nonzero norm is invertible. -/
def rightMulEquiv (v : Carrier F) (hv : norm v ≠ 0) : Carrier F ≃ₗ[F] Carrier F where
  toLinearMap := multiplication.flip v
  invFun y := (norm v)⁻¹ • mul y (conjugate v)
  left_inv x := by
    change (norm v)⁻¹ • mul (mul x v) (conjugate v) = x
    rw [mul_mul_conjugate_right, smul_smul, inv_mul_cancel₀ hv, one_smul]
  right_inv y := by
    change mul ((norm v)⁻¹ • mul y (conjugate v)) v = y
    rw [smul_mul, mul_conjugate_mul_right, smul_smul, inv_mul_cancel₀ hv, one_smul]

@[simp] theorem rightMulEquiv_apply (v : Carrier F) (hv : norm v ≠ 0) (x : Carrier F) :
    rightMulEquiv v hv x = mul x v := rfl

@[simp] theorem rightMulEquiv_symm_apply (v : Carrier F) (hv : norm v ≠ 0)
    (x : Carrier F) :
    (rightMulEquiv v hv).symm x = (norm v)⁻¹ • mul x (conjugate v) := rfl

end Atlas.SplitOctonion
