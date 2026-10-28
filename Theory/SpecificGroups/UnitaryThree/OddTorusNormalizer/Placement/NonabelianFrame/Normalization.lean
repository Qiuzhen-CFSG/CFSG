module

public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.NonabelianFrame.Basic
public import BenderSuzuki.External.Huppert.II.theorem_10_4
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Normalizing a diagonal Hermitian frame over its original field

Nondegeneracy makes each diagonal Gram entry nonzero and Hermitian symmetry
makes it a fixed-field element. Surjectivity of the quadratic finite-field
norm supplies a separate rescaling of each column. The resulting Gram matrix
is the identity, and all three projective lines remain unchanged. Hence every
element of the original line stabilizer preserves the normalized frame and
normalizes its actual special-unitary torus.

The Gram-diagonal and line-invariance hypotheses are explicit intermediate
premises. This module does not assert their existence for an arbitrary odd
subgroup. The final nonabelian branch must discharge both of them.

Sources: Huppert II.10.4; GLS4, Chapter 4, Lemma 3.11(a),
`refs/KGroup/GLS4/Chapter4.tex`, lines 585–603. The rescaling calculation adapts
the repository's Chapter 1 `ModTwoExtraspecial/Placement/OrthogonalFrames.lean`
argument, using arbitrary fixed-field cardinality and actual projective lines.
-/

public section

open Matrix BenderSuzuki.MatrixGroups BenderSuzuki.External
open scoped Pointwise LinearAlgebra.Projectivization
namespace UnitaryThree.OddTorusNormalizer.NonabelianFrame
variable {E : Type*} [Field E]

private theorem adjoint_mul (J : HermitianForm 3 E) (A B : Matrix (Fin 3) (Fin 3) E) :
    J.conjTranspose (A * B) = J.conjTranspose B * J.conjTranspose A := by
  change ((J.conj : E →+* E).mapMatrix (A * B)).transpose = _
  rw [map_mul, transpose_mul]
  rfl

private theorem adjoint_diagonal (J : HermitianForm 3 E) (d : Fin 3 → E) :
    J.conjTranspose (diagonal d) = diagonal (fun i => J.conj (d i)) := by
  ext i j
  by_cases h : i = j
  · subst j; simp [HermitianForm.conjTranspose]
  · simp [HermitianForm.conjTranspose, diagonal_apply_ne _ h,
      diagonal_apply_ne _ (Ne.symm h)]

/-- A diagonal Gram matrix can be normalized over the actual quadratic field
without changing any of the three projective column lines. -/
theorem orthogonalFrame_of_diagonal_gram [Finite E]
    (J : HermitianForm 3 E) (q : ℕ) (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (C : GL (Fin 3) E) (hdiag : (J.conjTranspose C.val * J.form * C.val).IsDiag) :
    ∃ P : OrthogonalFrame J, frameLines P = C • Set.range (coordinateLine (E := E)) := by
  classical
  let : Star E := ⟨J.conj⟩
  let : InvolutiveStar E := ⟨J.conj_involutive⟩
  let : StarMul E := ⟨fun r s => by
    change J.conj (r * s) = J.conj s * J.conj r
    rw [map_mul, mul_comm]⟩
  let : StarRing E := ⟨fun r s => by
    change J.conj (r + s) = J.conj r + J.conj s
    rw [map_add]⟩
  let A : Matrix (Fin 3) (Fin 3) E := J.conjTranspose C.val * J.form * C.val
  change A.IsDiag at hdiag
  have hAherm : A.IsHermitian := by
    apply Matrix.isHermitian_conjTranspose_mul_mul
    exact Matrix.IsHermitian.ext J.form_hermitian
  have hAdet : A.det ≠ 0 := by
    change (C.valᴴ * J.form * C.val).det ≠ 0
    rw [det_mul, det_mul, det_conjTranspose]
    exact mul_ne_zero (mul_ne_zero (star_ne_zero.mpr C.det_ne_zero)
      J.form_nondegenerate) C.det_ne_zero
  have ha0 (i : Fin 3) : A i i ≠ 0 := by
    have he := hdiag.diagonal_diag
    change diagonal A.diag = A at he
    rw [← he, det_diagonal] at hAdet
    exact (Finset.prod_ne_zero_iff.mp hAdet) i (Finset.mem_univ i)
  have hs (i : Fin 3) : ∃ d : E, d ≠ 0 ∧ d * J.conj d = (A i i)⁻¹ :=
    huppert_II_10_4_norm_surjective J q hcard hfixed _
      (by
        rw [map_inv₀]
        exact congrArg Inv.inv (show J.conj (A i i) = A i i from hAherm.apply i i)) (inv_ne_zero (ha0 i))
  choose d hd0 hd using hs
  let D : GL (Fin 3) E := GeneralLinearGroup.mkOfDetNeZero (diagonal d)
    (by rw [det_diagonal]; exact Finset.prod_ne_zero_iff.mpr (fun i _ => hd0 i))
  have hDl (i : Fin 3) : D • coordinateLine (E := E) i = coordinateLine i := by
    rw [coordinateLine, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
    refine ⟨Units.mk0 (d i) (hd0 i), ?_⟩
    change (d i) • Pi.single i 1 = diagonal d *ᵥ Pi.single i 1
    ext j
    by_cases hij : j = i
    · subst j; simp
    · simp [hij]
  have hDr : D • Set.range (coordinateLine (E := E)) = Set.range coordinateLine := by
    ext l
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      change D • coordinateLine i ∈ Set.range coordinateLine
      rw [hDl]
      exact Set.mem_range_self i
    · rintro ⟨i, rfl⟩
      exact ⟨_, Set.mem_range_self i, hDl i⟩
  have hgram : J.conjTranspose (C * D).val * J.form * (C * D).val = 1 := by
    change J.conjTranspose (C.val * diagonal d) * J.form * (C.val * diagonal d) = 1
    rw [adjoint_mul, adjoint_diagonal]
    have he : (diagonal (fun i => J.conj (d i)) * J.conjTranspose C.val) *
        J.form * (C.val * diagonal d) =
        diagonal (fun i => J.conj (d i)) * A * diagonal d := by
      simp only [A, mul_assoc]
    rw [he]
    ext i j
    simp only [diagonal_mul, mul_diagonal]
    by_cases hij : i = j
    · subst j
      rw [one_apply_eq]
      calc
        J.conj (d i) * A i i * d i = A i i * (d i * J.conj (d i)) := by ring
        _ = 1 := by rw [hd, mul_inv_cancel₀ (ha0 i)]
    · rw [hdiag hij, mul_zero, zero_mul, one_apply_ne hij]
  refine ⟨⟨C * D, hgram⟩, ?_⟩
  change (C * D) • Set.range coordinateLine = _
  rw [mul_smul, hDr]

/-- Normalization retains the whole subgroup's actual action on the frame. -/
theorem specialFrameStabilizer_of_diagonal_gram [Finite E]
    (J : HermitianForm 3 E) (q : ℕ) (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (K : Subgroup J.specialSubgroup) (C : GL (Fin 3) E)
    (hpres : PreservesLines J K C)
    (hdiag : (J.conjTranspose C.val * J.form * C.val).IsDiag) :
    ∃ P : OrthogonalFrame J, K ≤ specialFrameStabilizer J P := by
  obtain ⟨P, hP⟩ := orthogonalFrame_of_diagonal_gram J q hcard hfixed C hdiag
  refine ⟨P, fun g hg => ?_⟩
  change g.val • frameLines P = frameLines P
  rw [hP]
  exact hpres g hg

/-- The normalized frame yields containment in the normalizer of the literal
special-unitary frame torus. The invariant lines and Gram condition remain
explicit geometric premises. -/
theorem specialFrameTorus_normalizer_of_diagonal_gram [Finite E]
    (J : HermitianForm 3 E) (q : ℕ) (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (K : Subgroup J.specialSubgroup) (C : GL (Fin 3) E)
    (hpres : PreservesLines J K C)
    (hdiag : (J.conjTranspose C.val * J.form * C.val).IsDiag) :
    ∃ P : OrthogonalFrame J, K ≤ Subgroup.normalizer (specialFrameTorus J P) := by
  obtain ⟨P, hP⟩ := specialFrameStabilizer_of_diagonal_gram J q hcard hfixed K C hpres hdiag
  exact ⟨P, hP.trans (specialFrameStabilizer_le_normalizer J P)⟩

end UnitaryThree.OddTorusNormalizer.NonabelianFrame
