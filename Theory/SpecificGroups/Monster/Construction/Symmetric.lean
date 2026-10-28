module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum

/-!
# The symmetric-matrix summand of the Griess algebra

The summand `SymmetricPart` is the space of real symmetric 24-by-24 matrices.
Its bilinear form is `trace (A * B)` and its product is `2 • (A * B + B * A)`.
Upper-triangular coordinates give dimension 300. The trace form is positive
because its value on `(A, A)` is the sum of the squared matrix entries.
Cyclicity of trace proves symmetry of the induced trilinear form; orthogonal
conjugation preserves both forms and the multiplication.

Source: Aschbacher, *Sporadic Groups* (1994), Section 27, pp. 149–150,
(28.1) and Lemma 28.7, pp. 151–152; see also Conway et al., *Atlas of Finite
Groups* (1985), Monster entry, PDF pp. 262–264. The normalization gives squared
length 1 to a diagonal basis vector and squared length 2 to an off-diagonal
symmetric basis vector. This module constructs only the 300-dimensional
summand; the other summands and their mixed products are separate obligations.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace Sporadic.Monster.Construction

/-- The symmetric-matrix summand of the Griess algebra. -/
def symmetricMatrices : Submodule ℝ (Matrix (Fin 24) (Fin 24) ℝ) where
  carrier := {A | A.IsSymm}
  zero_mem' := Matrix.isSymm_zero
  add_mem' := Matrix.IsSymm.add
  smul_mem' c _ h := h.smul c

abbrev SymmetricPart := symmetricMatrices

def symmetricGamma (A B : SymmetricPart) : ℝ :=
  Matrix.trace (A.val * B.val)

theorem symmetricGamma_comm (A B : SymmetricPart) :
    symmetricGamma A B = symmetricGamma B A := Matrix.trace_mul_comm _ _

theorem symmetricGamma_add_left (A B C : SymmetricPart) :
    symmetricGamma (A + B) C = symmetricGamma A C + symmetricGamma B C := by
  simp [symmetricGamma, Matrix.add_mul]

theorem symmetricGamma_smul_left (r : ℝ) (A B : SymmetricPart) :
    symmetricGamma (r • A) B = r * symmetricGamma A B := by
  simp [symmetricGamma]

theorem symmetricGamma_self (A : SymmetricPart) :
    symmetricGamma A A = ∑ i, ∑ j, A.val i j ^ 2 := by
  unfold symmetricGamma Matrix.trace
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [A.property.apply i j, pow_two]

theorem symmetricGamma_nonneg (A : SymmetricPart) : 0 ≤ symmetricGamma A A := by
  rw [symmetricGamma_self]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

theorem symmetricGamma_eq_zero_iff (A : SymmetricPart) :
    symmetricGamma A A = 0 ↔ A = 0 := by
  constructor
  · intro h
    rw [symmetricGamma_self] at h
    have hrow := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) =>
        Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => sq_nonneg (A.val i j)))).mp h
    apply Subtype.ext
    ext i j
    have hij := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ Finset.univ) => sq_nonneg (A.val i j))).mp
        (hrow i (Finset.mem_univ i)) j (Finset.mem_univ j)
    exact (sq_eq_zero_iff.mp hij)
  · rintro rfl
    simp [symmetricGamma]

theorem symmetricGamma_pos (A : SymmetricPart) (h : A ≠ 0) :
    0 < symmetricGamma A A :=
  lt_of_le_of_ne (symmetricGamma_nonneg A)
    (fun he => h ((symmetricGamma_eq_zero_iff A).mp he.symm))

/-- Aschbacher (28.1), including the factor of two. -/
def symmetricProduct (A B : SymmetricPart) : SymmetricPart :=
  ⟨(2 : ℝ) • (A.val * B.val + B.val * A.val), by
    change ((2 : ℝ) • (A.val * B.val + B.val * A.val)).IsSymm
    apply Matrix.IsSymm.smul
    change (A.val * B.val + B.val * A.val)ᵀ = _
    rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul,
      A.property.eq, B.property.eq, add_comm]⟩

theorem symmetricProduct_comm (A B : SymmetricPart) :
    symmetricProduct A B = symmetricProduct B A := by
  apply Subtype.ext
  simp only [symmetricProduct, add_comm]

theorem symmetricProduct_add_left (A B C : SymmetricPart) :
    symmetricProduct (A + B) C = symmetricProduct A C + symmetricProduct B C := by
  apply Subtype.ext
  change (2 : ℝ) • ((A.val + B.val) * C.val + C.val * (A.val + B.val)) = _
  simp only [Matrix.add_mul, Matrix.mul_add, smul_add, symmetricProduct,
    Submodule.coe_add]
  abel

theorem symmetricProduct_smul_left (r : ℝ) (A B : SymmetricPart) :
    symmetricProduct (r • A) B = r • symmetricProduct A B := by
  apply Subtype.ext
  change (2 : ℝ) • ((r • A.val) * B.val + B.val * (r • A.val)) = _
  change (2 : ℝ) • ((r • A.val) * B.val + B.val * (r • A.val)) =
    r • ((2 : ℝ) • (A.val * B.val + B.val * A.val))
  rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_add, smul_comm]

/-- The restriction of the Griess trilinear form to the symmetric summand. -/
def symmetricBeta (A B C : SymmetricPart) : ℝ :=
  symmetricGamma (symmetricProduct A B) C

theorem symmetricBeta_swap_left (A B C : SymmetricPart) :
    symmetricBeta A B C = symmetricBeta B A C := by
  rw [symmetricBeta, symmetricProduct_comm, symmetricBeta]

theorem symmetricBeta_swap_right (A B C : SymmetricPart) :
    symmetricBeta A B C = symmetricBeta A C B := by
  simp only [symmetricBeta, symmetricGamma, symmetricProduct, Matrix.smul_mul,
    Matrix.add_mul, Matrix.trace_smul, Matrix.trace_add, smul_eq_mul]
  have h₁ : Matrix.trace (A.val * B.val * C.val) =
      Matrix.trace (C.val * A.val * B.val) := Matrix.trace_mul_cycle _ _ _
  have h₂ : Matrix.trace (B.val * A.val * C.val) =
      Matrix.trace (A.val * C.val * B.val) := (Matrix.trace_mul_cycle _ _ _).symm
  rw [h₁, h₂, add_comm]

abbrev SymmetricCoordinate := {p : Fin 24 × Fin 24 // p.1 ≤ p.2}

/-- Upper-triangular entries give coordinates on the symmetric summand. -/
def symmetricCoordinates : SymmetricPart ≃ₗ[ℝ] (SymmetricCoordinate → ℝ) where
  toFun A p := A.val p.val.1 p.val.2
  invFun a := ⟨Matrix.of (fun i j => if h : i ≤ j then a ⟨(i, j), h⟩
    else a ⟨(j, i), le_of_not_ge h⟩), by
      apply Matrix.IsSymm.ext
      intro i j
      dsimp
      split_ifs with h₁ h₂ h₂
      · have : i = j := le_antisymm h₂ h₁
        subst j
        rfl
      · rfl
      · rfl
      · exact False.elim (h₁ (le_of_not_ge h₂))⟩
  left_inv A := by
    apply Subtype.ext
    ext i j
    dsimp
    split_ifs with h
    · rfl
    · exact A.property.apply i j
  right_inv a := by
    funext p
    dsimp
    rw [dif_pos p.property]
  map_add' A B := rfl
  map_smul' r A := rfl

set_option maxRecDepth 2048 in
theorem symmetricCoordinate_card : Fintype.card SymmetricCoordinate = 300 := by decide

theorem symmetricPart_finrank : Module.finrank ℝ SymmetricPart = 300 := by
  rw [symmetricCoordinates.finrank_eq, Module.finrank_fintype_fun_eq_card,
    symmetricCoordinate_card]

/-- The bilinear form on the symmetric summand, bundled for direct sums. -/
def symmetricGammaForm : SymmetricPart →ₗ[ℝ] SymmetricPart →ₗ[ℝ] ℝ where
  toFun A :=
    { toFun := symmetricGamma A
      map_add' B C := by
        rw [symmetricGamma_comm, symmetricGamma_add_left,
          symmetricGamma_comm B, symmetricGamma_comm C]
      map_smul' r B := by
        simp only [symmetricGamma_comm A, symmetricGamma_smul_left, smul_eq_mul, RingHom.id_apply] }
  map_add' A B := by
    ext C
    exact symmetricGamma_add_left A B C
  map_smul' r A := by
    ext B
    exact symmetricGamma_smul_left r A B

/-- The symmetric-summand multiplication as a bilinear map. -/
def symmetricProductMap : SymmetricPart →ₗ[ℝ] SymmetricPart →ₗ[ℝ] SymmetricPart where
  toFun A :=
    { toFun := symmetricProduct A
      map_add' B C := by
        rw [symmetricProduct_comm, symmetricProduct_add_left,
          symmetricProduct_comm B, symmetricProduct_comm C]
      map_smul' r B := by
        rw [symmetricProduct_comm, symmetricProduct_smul_left, symmetricProduct_comm]
        rfl }
  map_add' A B := by
    apply LinearMap.ext
    intro C
    exact symmetricProduct_add_left A B C
  map_smul' r A := by
    apply LinearMap.ext
    intro B
    exact symmetricProduct_smul_left r A B

/-- One quarter of the identity matrix is the unit in this summand. -/
noncomputable def symmetricUnit : SymmetricPart :=
  ⟨(1 / 4 : ℝ) • (1 : Matrix (Fin 24) (Fin 24) ℝ), Matrix.isSymm_one.smul _⟩

theorem symmetricUnit_product (A : SymmetricPart) :
    symmetricProduct symmetricUnit A = A := by
  apply Subtype.ext
  change (2 : ℝ) • (((1 / 4 : ℝ) • 1) * A.val +
    A.val * ((1 / 4 : ℝ) • 1)) = A.val
  simp only [Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, ← add_smul, smul_smul]
  norm_num

/-- The action on symmetric tensors induced by a matrix on the natural space. -/
def symmetricConjugate (P : Matrix (Fin 24) (Fin 24) ℝ)
    (A : SymmetricPart) : SymmetricPart :=
  ⟨Pᵀ * A.val * P, by
    change (Pᵀ * A.val * P)ᵀ = Pᵀ * A.val * P
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      A.property.eq, Matrix.mul_assoc]⟩

private theorem conjugate_mul (P A B : Matrix (Fin 24) (Fin 24) ℝ)
    (hP : P * Pᵀ = 1) :
    (Pᵀ * A * P) * (Pᵀ * B * P) = Pᵀ * (A * B) * P := by
  calc
    _ = Pᵀ * A * (P * Pᵀ) * B * P := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hP]; simp only [mul_one, Matrix.mul_assoc]

theorem symmetricConjugate_product (P : Matrix (Fin 24) (Fin 24) ℝ)
    (hP : P * Pᵀ = 1) (A B : SymmetricPart) :
    symmetricProduct (symmetricConjugate P A) (symmetricConjugate P B) =
      symmetricConjugate P (symmetricProduct A B) := by
  apply Subtype.ext
  change (2 : ℝ) • ((Pᵀ * A.val * P) * (Pᵀ * B.val * P) +
    (Pᵀ * B.val * P) * (Pᵀ * A.val * P)) =
      Pᵀ * ((2 : ℝ) • (A.val * B.val + B.val * A.val)) * P
  rw [conjugate_mul P _ _ hP, conjugate_mul P _ _ hP]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]

theorem symmetricConjugate_gamma (P : Matrix (Fin 24) (Fin 24) ℝ)
    (hP : P * Pᵀ = 1) (A B : SymmetricPart) :
    symmetricGamma (symmetricConjugate P A) (symmetricConjugate P B) =
      symmetricGamma A B := by
  change Matrix.trace ((Pᵀ * A.val * P) * (Pᵀ * B.val * P)) = _
  rw [conjugate_mul P _ _ hP, Matrix.trace_mul_cycle, hP, one_mul]
  rfl

theorem symmetricConjugate_beta (P : Matrix (Fin 24) (Fin 24) ℝ)
    (hP : P * Pᵀ = 1) (A B C : SymmetricPart) :
    symmetricBeta (symmetricConjugate P A) (symmetricConjugate P B)
      (symmetricConjugate P C) = symmetricBeta A B C := by
  unfold symmetricBeta
  rw [symmetricConjugate_product P hP, symmetricConjugate_gamma P hP]

end Sporadic.Monster.Construction
