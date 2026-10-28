module
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Descent.SymmetricSimilarity.FiniteForms
public import BenderSuzuki.MatrixGroups.Unitary
public import Mathlib.Algebra.Ring.Action.End
public import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Tactic

/-!
# Similarity of fixed symmetric ternary forms in odd characteristic

A symmetric matrix fixed by the Hermitian involution is a matrix over its
actual fixed subfield. Over that finite odd field, the determinant square class
classifies nondegenerate quadratic forms. If `d` is the determinant of the given
matrix, scaling the antidiagonal target by `-d` makes the ratio of discriminants
`d²`. The resulting quadratic isometry gives a genuine matrix congruence.
Mapping this matrix back to the original field preserves invertibility and
makes every entry fixed by conjugation.

This supplies exactly the fixed-field similarity input of
`Descent.projective_descent_of_linear_and_similarity`, including `p = 3`.
The ambient field cardinality is retained in the interface; the proof needs
only the finite fixed field of odd order. No scalar norm correction is used.

Source: GLS3, §§2.7 and 4.3; Aschbacher–Smith F.6.18(10)–(11), printed
pp.309–310. The finite-field classification port is attributed and licensed
in `SymmetricSimilarity/FiniteForms.lean`.
-/

open Matrix
noncomputable section
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Descent
variable {F : Type*} [Field F] [Invertible (2 : F)]
private theorem matrix_form_matrix (S : Matrix (Fin 3) (Fin 3) F) (hs : S.transpose = S) :
    S.toQuadraticForm'.toMatrix' = S := by
  have hB := Matrix.isSymm_toBilin'_iff_isSymm.mpr hs
  change LinearMap.toMatrix₂' F (QuadraticMap.associated S.toBilin'.toQuadraticMap) = S
  rw [QuadraticMap.associated_left_inverse F (fun x y => hB.eq x y)]
  exact LinearMap.toMatrix'_toLinearMap₂' S

private theorem polar_nondegenerate (Q : QuadraticForm F (Fin 3 → F)) (h2 : (2 : F) ≠ 0)
    (hQ : Q.toMatrix'.det ≠ 0) : Q.polarBilin.Nondegenerate := by
  have ha : Q.associated.Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toMatrix'_iff.mp
      (Matrix.nondegenerate_iff_det_ne_zero.mpr hQ)
  constructor
  · intro x hx
    apply ha.1
    intro y
    have h := congrArg (fun B => B x y) (QuadraticMap.two_nsmul_associated (S := F) Q)
    simp only [LinearMap.smul_apply, nsmul_eq_mul, hx] at h
    exact (mul_eq_zero.mp h).resolve_left h2
  · intro x hx
    apply ha.2
    intro y
    have h := congrArg (fun B => B y x) (QuadraticMap.two_nsmul_associated (S := F) Q)
    simp only [LinearMap.smul_apply, nsmul_eq_mul, hx] at h
    exact (mul_eq_zero.mp h).resolve_left h2

private theorem ternary_similarity [Finite F] (h2 : (2 : F) ≠ 0)
    (S : Matrix (Fin 3) (Fin 3) F) (hs : S.transpose = S) (hd : S.det ≠ 0) :
    ∃ (a : F) (C : GL (Fin 3) F), a ≠ 0 ∧
      C.val.transpose * S * C.val = a • !![0, 0, 1; 0, 1, 0; 1, 0, 0] := by
  let T : Matrix (Fin 3) (Fin 3) F := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  have ht : T.transpose = T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have htd : T.det = -1 := by simp [T, Matrix.det_fin_three]
  let a := -S.det
  have ha : a ≠ 0 := neg_ne_zero.mpr hd
  let Q := S.toQuadraticForm'
  let R := a • T.toQuadraticForm'
  have hQ : Q.toMatrix' = S := matrix_form_matrix S hs
  have hR : R.toMatrix' = a • T := by
    rw [QuadraticForm.toMatrix'_smul, matrix_form_matrix T ht]
  have hRd : R.discr' = S.det ^ 3 := by
    rw [QuadraticForm.discr', hR, Matrix.det_smul, htd]
    simp only [a, Fintype.card_fin, mul_neg, mul_one]
    ring
  have hQd : Q.discr' = S.det := congrArg Matrix.det hQ
  obtain ⟨e⟩ := (SymmetricSimilarity.finite_nondegenerate_isometry_iff_discr_square h2 2 R Q
    (polar_nondegenerate R h2 (by change R.discr' ≠ 0; rw [hRd]; exact pow_ne_zero _ hd))
    (polar_nondegenerate Q h2 (by rwa [hQ]))).mpr (by
      rw [hRd, hQd]
      refine ⟨S.det, ?_⟩
      field_simp)
  let M := LinearMap.toMatrix' e.toLinearEquiv.toLinearMap
  have hM : M.det ≠ 0 := by
    rw [LinearMap.det_toMatrix']
    exact e.toLinearEquiv.isUnit_det'.ne_zero
  refine ⟨a, GeneralLinearGroup.mkOfDetNeZero M hM, ha, ?_⟩
  have he : Q.comp e.toLinearEquiv.toLinearMap = R := by
    ext v
    exact e.map_app v
  have h := congrArg QuadraticForm.toMatrix' he
  rw [QuadraticForm.toMatrix'_comp, hQ, hR] at h
  exact h


/-- A nonsingular fixed symmetric ternary matrix is congruent, over the fixed
field, to a nonzero fixed scalar multiple of the prescribed Hermitian matrix.
The scalar accounts for the two possible discriminant square classes. -/
public theorem fixed_symmetric_ternary_similarity
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {p : ℕ} (hp : p.Prime) (hmod : p % 8 = 3)
    (_hcard : Nat.card E = p ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = p)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (S : Matrix (Fin 3) (Fin 3) E)
    (hs : S.transpose = S) (hfix : S.map J.conj = S) (hd : S.det ≠ 0) :
    ∃ (a : E) (C : GL (Fin 3) E), a ≠ 0 ∧ J.conj a = a ∧
      C.val.map J.conj = C.val ∧ C.val.transpose * S * C.val = a • J.form := by
  let K := FixedBy.subfield E J.conj
  let : Fact p.Prime := ⟨hp⟩
  let := Fintype.ofFinite K
  have hk : Fintype.card K = p := by
    change Nat.card K = p at hfixed
    simpa only [Nat.card_eq_fintype_card] using hfixed
  let := charP_of_card_eq_prime hk
  have h2 : (2 : K) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime K (p := p)
    Nat.prime_two (by intro h; have hm := hmod; rw [h] at hm; norm_num at hm)
  let := invertibleOfNonzero h2
  let S₀ : Matrix (Fin 3) (Fin 3) K := fun i j =>
    ⟨S i j, congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M i j) hfix⟩
  have hm : S₀.map K.subtype = S := rfl
  have hs₀ : S₀.transpose = S₀ := by
    ext i j
    exact congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M i j) hs
  have hd₀ : S₀.det ≠ 0 := by
    intro h
    apply hd
    have hh := congrArg K.subtype h
    rw [RingHom.map_det, map_zero] at hh
    exact hh
  obtain ⟨a, C, ha, hC⟩ := ternary_similarity h2 S₀ hs₀ hd₀
  refine ⟨a.val, GeneralLinearGroup.map K.subtype C, ?_, a.property, ?_, ?_⟩
  · exact fun h => ha (Subtype.ext h)
  · ext i j
    exact (C.val i j).property
  · have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M.map K.subtype) hC
    change (C.val.map K.subtype).transpose * S * C.val.map K.subtype = a.val • J.form
    rw [hJ]
    have ht : ((a • !![0, 0, 1; 0, 1, 0; 1, 0, 0]) : Matrix (Fin 3) (Fin 3) K).map
        K.subtype = a.val • !![0, 0, 1; 0, 1, 0; 1, 0, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    simpa only [Matrix.map_mul, Matrix.transpose_map, hm, ht] using hh

end BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Descent
