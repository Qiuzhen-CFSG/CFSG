module

public import Theory.Representation.HermitianTensorThree.ImageOuter.Overgroups

/-!
# Congruence and coefficient actions on the Hermitian tensor

All GL₃ matrices act on the literal descended space by congruence. Entrywise
coefficient automorphisms preserve this space because they commute with its
Frobenius. Both actions normalize the given SL₃ image. Every fixed-field scalar
is a scalar-matrix congruence, by taking its square root in the fixed field.
The congruence kernel consists exactly of norm-one scalar matrices.

These constructions retain the inner-diagonal extension required in
Aschbacher–Smith, combined manuscript of 1 March 2004, H.4.2 setup and
H.4.6(3), printed pp.380–382. Coverage of the normalizer is a separate theorem.
-/

@[expose] public section
noncomputable section
namespace Representation.HermitianTensorThree.ImageOuter
variable (n : ℕ) [NeZero n]

/-- All invertible matrices act by congruence on the fixed space. -/
def congruence (g : Matrix.GeneralLinearGroup (Fin 3) (E n)) :
    Space n ≃ₗ[F n] Space n where
  toFun X := ⟨g.val * X.val * adjoint n g.val, by
    change adjoint n (g.val * X.val * adjoint n g.val) = _
    rw [adjoint_mul, adjoint_mul, adjoint_involutive n, X.property, Matrix.mul_assoc]⟩
  invFun X := ⟨g.inv * X.val * adjoint n g.inv, by
    change adjoint n (g.inv * X.val * adjoint n g.inv) = _
    rw [adjoint_mul, adjoint_mul, adjoint_involutive n, X.property, Matrix.mul_assoc]⟩
  left_inv X := by
    apply Subtype.ext
    change g.inv * (g.val * X.val * adjoint n g.val) * adjoint n g.inv = X.val
    calc
      _ = (g.inv * g.val) * X.val * adjoint n (g.inv * g.val) := by
        rw [adjoint_mul]; simp only [Matrix.mul_assoc]
      _ = X.val := by rw [g.inv_val, adjoint_one, one_mul, mul_one]
  right_inv X := by
    apply Subtype.ext
    change g.val * (g.inv * X.val * adjoint n g.inv) * adjoint n g.val = X.val
    calc
      _ = (g.val * g.inv) * X.val * adjoint n (g.val * g.inv) := by
        rw [adjoint_mul]; simp only [Matrix.mul_assoc]
      _ = X.val := by rw [g.val_inv, adjoint_one, one_mul, mul_one]
  map_add' X Y := by apply Subtype.ext; simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by apply Subtype.ext; simp

def congruenceHom : Matrix.GeneralLinearGroup (Fin 3) (E n) →*
    (Space n ≃ₗ[F n] Space n) where
  toFun := congruence n
  map_one' := by
    apply LinearEquiv.ext; intro X; apply Subtype.ext
    change (1 : Mat n) * X.val * adjoint n 1 = X.val
    rw [adjoint_one, one_mul, mul_one]
  map_mul' g h := by
    apply LinearEquiv.ext; intro X; apply Subtype.ext
    change (g.val * h.val) * X.val * adjoint n (g.val * h.val) =
      g.val * (h.val * X.val * adjoint n h.val) * adjoint n g.val
    rw [adjoint_mul]; simp only [Matrix.mul_assoc]

def binaryCongruence : Matrix.GeneralLinearGroup (Fin 3) (E n) →*
    (Space n ≃ₗ[ZMod 2] Space n) := (binaryEquivHom n).comp (congruenceHom n)

theorem binaryCongruence_apply (g : Matrix.GeneralLinearGroup (Fin 3) (E n)) (X : Space n) :
    (binaryCongruence n g X).val = g.val * X.val * adjoint n g.val := rfl

theorem binaryCongruence_toGL (g : Cover n) :
    binaryCongruence n (Matrix.SpecialLinearGroup.toGL g) = binaryActionHom n g := by
  apply LinearEquiv.ext; intro X; rfl

omit [NeZero n] in
/-- Coefficient automorphisms commute with the prescribed Frobenius. -/
theorem sigma_map (τ : E n ≃+* E n) (c : E n) :
    sigma n (τ c) = τ (sigma n c) := by
  change iterateFrobeniusEquiv (E n) 2 n (τ c) = τ (iterateFrobeniusEquiv (E n) 2 n c)
  simp only [iterateFrobeniusEquiv_def, map_pow]

omit [NeZero n] in
theorem adjoint_map (τ : E n ≃+* E n) (X : Mat n) :
    adjoint n (X.map τ) = (adjoint n X).map τ := by
  ext i j; exact sigma_map n τ (X j i)

/-- Coefficient action on the literal binary Hermitian space. -/
def coefficient (τ : E n ≃+* E n) : Space n ≃ₗ[ZMod 2] Space n :=
  let e : Space n ≃+ Space n := {
    toFun X := ⟨X.val.map τ, by
      change adjoint n (X.val.map τ) = _
      rw [adjoint_map, X.property]⟩
    invFun X := ⟨X.val.map τ.symm, by
      change adjoint n (X.val.map τ.symm) = _
      rw [adjoint_map, X.property]⟩
    left_inv X := by apply Subtype.ext; ext i j; exact τ.symm_apply_apply _
    right_inv X := by apply Subtype.ext; ext i j; exact τ.apply_symm_apply _
    map_add' X Y := by apply Subtype.ext; ext i j; exact map_add τ _ _ }
  { __ := e
    map_smul' := e.toAddMonoidHom.toZModLinearMap 2 |>.map_smul }

theorem coefficient_apply (τ : E n ≃+* E n) (X : Space n) :
    (coefficient n τ X).val = X.val.map τ := rfl

theorem coefficient_symm (τ : E n ≃+* E n) :
    (coefficient n τ)⁻¹ = coefficient n τ.symm := by
  apply LinearEquiv.ext; intro X; rfl

/-- The marked field involution is the corresponding coefficient action. -/
theorem coefficient_sigma : coefficient n (sigma n) = fieldSwapBinary n := by
  apply LinearEquiv.ext; intro X; apply Subtype.ext
  exact (fieldSwap_eq_map n X).symm

/-- The standard semilinear congruence on the actual descended space. -/
def semilinearCongruence (g : Matrix.GeneralLinearGroup (Fin 3) (E n))
    (τ : E n ≃+* E n) : Space n ≃ₗ[ZMod 2] Space n :=
  binaryCongruence n g * coefficient n τ

theorem semilinearCongruence_apply (g : Matrix.GeneralLinearGroup (Fin 3) (E n))
    (τ : E n ≃+* E n) (X : Space n) :
    (semilinearCongruence n g τ X).val =
      g.val * X.val.map τ * adjoint n g.val := rfl

private def coverConj (g : Matrix.GeneralLinearGroup (Fin 3) (E n)) (a : Cover n) : Cover n :=
  ⟨(g * Matrix.SpecialLinearGroup.toGL a * g⁻¹).val, by
    change (g.val * a.val * g.inv).det = 1
    rw [Matrix.det_mul, Matrix.det_mul, a.property, mul_one,
      ← Matrix.det_mul, g.val_inv, Matrix.det_one]⟩

omit [NeZero n] in
private theorem coverConj_toGL (g : Matrix.GeneralLinearGroup (Fin 3) (E n)) (a : Cover n) :
    Matrix.SpecialLinearGroup.toGL (coverConj n g a) =
      g * Matrix.SpecialLinearGroup.toGL a * g⁻¹ := by ext : 1; rfl

theorem binaryCongruence_mem_normalizer (g : Matrix.GeneralLinearGroup (Fin 3) (E n)) :
    binaryCongruence n g ∈ binaryNormalizer n := by
  change binaryCongruence n g ∈ Subgroup.normalizer (binaryImage n : Set _)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have conj (g : Matrix.GeneralLinearGroup (Fin 3) (E n)) (a : Cover n) :
      binaryCongruence n g * binaryActionHom n a * (binaryCongruence n g)⁻¹ =
        binaryActionHom n (coverConj n g a) := by
    rw [← binaryCongruence_toGL n (coverConj n g a), coverConj_toGL,
      map_mul, map_mul, map_inv, binaryCongruence_toGL]
  apply le_antisymm
  · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨coverConj n g a, (conj g a).symm⟩
  · rintro _ ⟨a, rfl⟩
    refine ⟨binaryActionHom n (coverConj n g⁻¹ a), ⟨_, rfl⟩, ?_⟩
    change binaryCongruence n g * binaryActionHom n (coverConj n g⁻¹ a) *
      (binaryCongruence n g)⁻¹ = _
    rw [← conj g⁻¹ a, map_inv]
    simp [mul_assoc]

theorem coefficient_conj (τ : E n ≃+* E n) (a : Cover n) :
    coefficient n τ * binaryActionHom n a * (coefficient n τ)⁻¹ =
      binaryActionHom n (Matrix.SpecialLinearGroup.map τ.toRingHom a) := by
  apply LinearEquiv.ext; intro X; apply Subtype.ext
  change (a.val * (X.val.map τ.symm) * adjoint n a.val).map τ =
    a.val.map τ * X.val * adjoint n (a.val.map τ)
  rw [Matrix.map_mul, Matrix.map_mul, adjoint_map]
  have h : (X.val.map τ.symm).map τ = X.val := by ext i j; exact τ.apply_symm_apply _
  rw [h]

theorem coefficient_mem_normalizer (τ : E n ≃+* E n) :
    coefficient n τ ∈ binaryNormalizer n := by
  change coefficient n τ ∈ Subgroup.normalizer (binaryImage n : Set _)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply le_antisymm
  · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨Matrix.SpecialLinearGroup.map τ.toRingHom a, (coefficient_conj n τ a).symm⟩
  · rintro _ ⟨a, rfl⟩
    let b := Matrix.SpecialLinearGroup.map τ.symm.toRingHom a
    refine ⟨binaryActionHom n b, ⟨b, rfl⟩, ?_⟩
    change coefficient n τ * binaryActionHom n b * (coefficient n τ)⁻¹ = _
    rw [coefficient_conj]
    congr 1
    apply Subtype.ext; ext i j; exact τ.apply_symm_apply _

theorem semilinearCongruence_mem_normalizer (g : Matrix.GeneralLinearGroup (Fin 3) (E n))
    (τ : E n ≃+* E n) : semilinearCongruence n g τ ∈ binaryNormalizer n :=
  (binaryNormalizer n).mul_mem (binaryCongruence_mem_normalizer n g)
    (coefficient_mem_normalizer n τ)

theorem mem_normalizer_of_hasCongruenceExpression (e : Space n ≃ₗ[ZMod 2] Space n)
    (he : HasCongruenceExpression n e) : e ∈ binaryNormalizer n := by
  obtain ⟨g, τ, he⟩ := he
  have h : e = semilinearCongruence n g τ := by
    apply LinearEquiv.ext; intro X; exact Subtype.ext (he X)
  rw [h]; exact semilinearCongruence_mem_normalizer n g τ

/-- Scalar multiplication by the actual fixed coefficient field. -/
def fixedScalar (c : (F n)ˣ) : Space n ≃ₗ[ZMod 2] Space n :=
  binaryEquiv n (LinearEquiv.smulOfUnit c)

theorem fixedScalar_apply (c : (F n)ˣ) (X : Space n) :
    fixedScalar n c X = c.val • X := rfl

omit [NeZero n] in
theorem scalar_congruence (c : E n) (X : Mat n) :
    Matrix.scalar (Fin 3) c * X * adjoint n (Matrix.scalar (Fin 3) c) =
      (c * sigma n c) • X := by
  have had : adjoint n (Matrix.scalar (Fin 3) c) =
      Matrix.scalar (Fin 3) (sigma n c) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [adjoint, Matrix.scalar_apply]
    · simp [adjoint, Matrix.scalar_apply, hij]
  rw [had]
  ext i j
  simp only [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.smul_apply, smul_eq_mul]
  ring

/-- Every nonzero fixed-field scalar already occurs among GL₃ congruences. -/
theorem fixedScalar_eq_congruence (c : (F n)ˣ) :
    ∃ d : (E n)ˣ, fixedScalar n c = binaryCongruence n (Matrix.GeneralLinearGroup.scalar (Fin 3) d) := by
  obtain ⟨d, hd⟩ := surjective_frobenius (F n) 2 c.val
  have hd2 : d ^ 2 = c.val := hd
  have hd0 : d ≠ 0 := by
    intro hz
    exact c.ne_zero (by simpa [hz] using hd2.symm)
  have hdE : (d : E n) ≠ 0 := by exact_mod_cast hd0
  refine ⟨Units.mk0 (d : E n) hdE, ?_⟩
  apply LinearEquiv.ext; intro X; apply Subtype.ext
  rw [binaryCongruence_apply]
  change (c.val : E n) • X.val =
    Matrix.scalar (Fin 3) (d : E n) * X.val * adjoint n (Matrix.scalar (Fin 3) (d : E n))
  have hdσ : sigma n (d : E n) = d := d.property
  rw [scalar_congruence, hdσ, ← pow_two]
  exact congrArg (fun a : F n => (a : E n) • X.val) hd2.symm

theorem fixedScalar_mem_normalizer (c : (F n)ˣ) : fixedScalar n c ∈ binaryNormalizer n := by
  obtain ⟨d, hd⟩ := fixedScalar_eq_congruence n c
  rw [hd]; exact binaryCongruence_mem_normalizer n _

/-- The exact kernel for all GL₃ matrices, with no determinant-one restriction. -/
theorem mem_binaryCongruence_ker_iff (g : Matrix.GeneralLinearGroup (Fin 3) (E n)) :
    g ∈ (binaryCongruence n).ker ↔
      ∃ c : E n, g.val = Matrix.scalar (Fin 3) c ∧ c * sigma n c = 1 := by
  constructor
  · intro hg
    exact eq_scalar_of_fixes_hermitian n g.val
      (fun X => congrArg (fun e : Space n ≃ₗ[ZMod 2] Space n => (e X).val) hg)
  · rintro ⟨c, hc, hnorm⟩
    apply LinearEquiv.ext; intro X; apply Subtype.ext
    change g.val * X.val * adjoint n g.val = X.val
    rw [hc]; exact scalar_action n c hnorm X.val

/-- The full inner-diagonal congruence image, on the binary space. -/
def congruenceImage : Subgroup (Space n ≃ₗ[ZMod 2] Space n) := (binaryCongruence n).range

def toCongruenceImage : Matrix.GeneralLinearGroup (Fin 3) (E n) →* congruenceImage n :=
  (binaryCongruence n).rangeRestrict

theorem congruenceImage_le_normalizer : congruenceImage n ≤ binaryNormalizer n := by
  rintro _ ⟨g, rfl⟩; exact binaryCongruence_mem_normalizer n g

theorem binaryImage_le_congruenceImage : binaryImage n ≤ congruenceImage n := by
  rintro _ ⟨g, rfl⟩; exact ⟨Matrix.SpecialLinearGroup.toGL g, binaryCongruence_toGL n g⟩

/-- The existing fixed-field SL₃ image embeds by exactly the same action. -/
def imageToCongruenceImage : Image n →* congruenceImage n :=
  (Subgroup.inclusion (binaryImage_le_congruenceImage n)).comp (binaryImageEquiv n).toMonoidHom

theorem imageToCongruenceImage_toImage (g : Cover n) :
    imageToCongruenceImage n (toImage n g) =
      toCongruenceImage n (Matrix.SpecialLinearGroup.toGL g) :=
  Subtype.ext (binaryCongruence_toGL n g).symm

end Representation.HermitianTensorThree.ImageOuter
