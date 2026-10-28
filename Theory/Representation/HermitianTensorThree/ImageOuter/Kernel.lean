module

public import Theory.Representation.HermitianTensorThree.FieldInvolution

/-!
# Kernel of the descended Hermitian tensor action

A matrix fixing the Hermitian diagonal units has zero off-diagonal entries.
Fixing the symmetric off-diagonal units then makes its diagonal entries equal,
with norm one. For a determinant-one matrix the scalar also has cube one.
Conversely, these scalars fix every matrix, so the descended kernel equals
both the full tensor kernel and the kernel after restricting scalars to GF(2).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.4.4(7),
printed pp.380–381. The proof uses the published literal matrix and tensor actions.
-/

public section
noncomputable section
namespace Representation.HermitianTensorThree.ImageOuter
variable (n : ℕ) [NeZero n]
private def diagonalUnit (i : Fin 3) : Space n :=
  ⟨Matrix.single i i 1, by
    ext a b
    simp [adjoint, Matrix.single_apply]⟩

private theorem diagonalUnit_action (A : Mat n) (i a b : Fin 3) :
    (A * (diagonalUnit n i).val * adjoint n A) a b = A a i * sigma n (A b i) := by
  simp [diagonalUnit, Matrix.mul_apply, Matrix.single_apply, adjoint, ite_and]

private def symmetricUnit (i j : Fin 3) : Space n :=
  ⟨Matrix.single i j 1 + Matrix.single j i 1, by
    ext a b
    simp [adjoint, Matrix.single_apply, add_comm]⟩

private theorem diagonal_of_fixes (A : Mat n)
    (h : ∀ X : Space n, X.val.transpose = X.val → A * X.val * adjoint n A = X.val) :
    A = Matrix.diagonal (fun i => A i i) := by
  have off (a i : Fin 3) (hai : a ≠ i) : A a i = 0 := by
    have he := congrArg (fun X : Mat n => X a a) (h (diagonalUnit n i) (by simp [diagonalUnit]))
    rw [diagonalUnit_action] at he
    have hz : A a i * sigma n (A a i) = 0 := by
      simpa [diagonalUnit, Matrix.single_apply, hai, Ne.symm hai] using he
    rcases mul_eq_zero.mp hz with hz | hz
    · exact hz
    · exact (sigma n).injective (hz.trans (map_zero _).symm)
  ext a b
  by_cases hab : a = b
  · subst b; simp
  · simp [hab, off a b hab]

/-- Fixing the symmetric Hermitian matrices already forces a norm-one scalar. -/
theorem eq_scalar_of_fixes_symmetric (A : Mat n)
    (h : ∀ X : Space n, X.val.transpose = X.val → A * X.val * adjoint n A = X.val) :
    ∃ c : E n, A = Matrix.scalar (Fin 3) c ∧ c * sigma n c = 1 := by
  have hd := diagonal_of_fixes n A h
  have hn (i : Fin 3) : A i i * sigma n (A i i) = 1 := by
    have he := congrArg (fun X : Mat n => X i i) (h (diagonalUnit n i) (by simp [diagonalUnit]))
    rw [diagonalUnit_action] at he
    simpa only [diagonalUnit, Matrix.single_apply_same] using he
  have had : adjoint n A = Matrix.diagonal (fun i => sigma n (A i i)) := by
    conv_lhs => rw [hd]
    ext a b
    by_cases hab : a = b
    · subst b; simp [adjoint]
    · simp [adjoint, hab]
  have hequal (i : Fin 3) : A i i = A 0 0 := by
    by_cases hi : i = 0
    · subst i; rfl
    have he := congrArg (fun X : Mat n => X i 0) (h (symmetricUnit n i 0) (by simp [symmetricUnit, add_comm]))
    rw [had] at he
    conv_lhs at he => rw [hd]
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at he
    have he' : A i i * sigma n (A 0 0) = 1 := by
      simpa [symmetricUnit, Matrix.single_apply, hi, Ne.symm hi] using he
    exact mul_right_cancel₀ (right_ne_zero_of_mul_eq_one (hn 0)) (he'.trans (hn 0).symm)
  refine ⟨A 0 0, ?_, hn 0⟩
  rw [hd, Matrix.scalar_apply]
  congr 1
  exact funext hequal

theorem eq_scalar_of_fixes_hermitian (A : Mat n)
    (h : ∀ X : Space n, A * X.val * adjoint n A = X.val) :
    ∃ c : E n, A = Matrix.scalar (Fin 3) c ∧ c * sigma n c = 1 :=
  eq_scalar_of_fixes_symmetric n A (fun X _ => h X)

omit [NeZero n] in
/-- A norm-one scalar acts trivially on every matrix, hence on the full tensor. -/
theorem scalar_action (c : E n) (hc : c * sigma n c = 1) (X : Mat n) :
    Matrix.scalar (Fin 3) c * X * adjoint n (Matrix.scalar (Fin 3) c) = X := by
  have had : adjoint n (Matrix.scalar (Fin 3) c) =
      Matrix.scalar (Fin 3) (sigma n c) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [adjoint, Matrix.scalar_apply]
    · simp [adjoint, Matrix.scalar_apply, hij]
  rw [had]
  ext i j
  simp only [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  calc
    c * X i j * sigma n c = (c * sigma n c) * X i j := by ring
    _ = X i j := by rw [hc, one_mul]

theorem mem_actionHom_ker_iff (g : Cover n) :
    g ∈ (actionHom n).ker ↔
      ∃ c : E n, g.val = Matrix.scalar (Fin 3) c ∧ c ^ 3 = 1 ∧ c * sigma n c = 1 := by
  constructor
  · intro hg
    have hfix (X : Space n) : g.val * X.val * adjoint n g.val = X.val := by
      exact congrArg (fun e : Space n ≃ₗ[F n] Space n => (e X).val) hg
    obtain ⟨c, he, hc⟩ := eq_scalar_of_fixes_hermitian n g.val hfix
    refine ⟨c, he, ?_, hc⟩
    have hd := g.property
    rw [he] at hd
    simpa [Matrix.scalar_apply] using hd
  · rintro ⟨c, he, _, hc⟩
    apply LinearEquiv.ext
    intro X
    apply Subtype.ext
    change g.val * X.val * adjoint n g.val = X.val
    rw [he]
    exact scalar_action n c hc X.val

/-- Restricting to the descended fixed space loses none of the tensor action. -/
theorem actionHom_eq_one_iff_tensor (g : Cover n) :
    actionHom n g = 1 ↔ tensorAction n g = 1 := by
  constructor
  · intro hg
    obtain ⟨c, he, _, hc⟩ := (mem_actionHom_ker_iff n g).mp hg
    apply LinearMap.ext
    intro u
    apply (tensorCoordinates n).injective
    rw [tensorCoordinates_action, matrixAction_apply, he]
    exact scalar_action n c hc (tensorCoordinates n u)
  · intro hg
    apply LinearEquiv.ext
    intro X
    apply Subtype.ext
    have hx := tensorCoordinates_action n g ((tensorCoordinates n).symm X.val)
    rw [hg] at hx
    change g.val * X.val * adjoint n g.val = X.val
    simpa only [Module.End.one_apply, LinearEquiv.apply_symm_apply, matrixAction_apply] using hx.symm

/-- Equality of the descended and full-tensor kernels as actual subgroups. -/
theorem actionHom_ker_eq_tensor_ker : (actionHom n).ker = (tensorAction n).ker := by
  ext g
  exact actionHom_eq_one_iff_tensor n g

theorem binaryActionHom_ker_eq : (binaryActionHom n).ker = (actionHom n).ker := by
  ext g
  change binaryEquiv n (actionHom n g) = 1 ↔ actionHom n g = 1
  constructor
  · intro hg
    apply LinearEquiv.ext
    intro X
    exact congrArg (fun e : Space n ≃ₗ[ZMod 2] Space n => e X) hg
  · intro hg
    rw [hg]
    rfl
end Representation.HermitianTensorThree.ImageOuter
