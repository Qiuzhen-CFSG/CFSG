module
public import ABG.ChapterII.Section2.UnitaryDeterminantNorm
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# The norm-one image of the unitary determinant

The determinant of the original GU2 over GF(p^(2n)) has image exactly
the subgroup of units whose (p^n+1)-st power is one. The forward inclusion
is the determinant of the actual Hermitian equation. Conversely, every
such unit c occurs as the determinant of diag(c,1), whose defining
Hermitian equation reduces to the same norm-one equation.

This supplies the surjectivity needed to compute the indices in the
actual unitary determinant filtration. Only primality of p and n nonzero
are required; no oddness, ambient order formula, or abstract unitary
recognition is used. Source: ABG II.2 before Lemma 1, article page 17,
and the filtration comparison in II.3 Proposition 3.
-/

namespace ABG
open Matrix.GeneralLinearGroup

public theorem GU2_det_range
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    ((det : GL (Fin 2) (GaloisField p (2 * n)) →* (GaloisField p (2 * n))ˣ).comp
      (unitaryForm 2 p n hn).unitarySubgroup.subtype).range =
      rootsOfUnity (p ^ n + 1) (GaloisField p (2 * n)) := by
  ext c
  constructor
  · rintro ⟨A, rfl⟩
    exact GU2_det_pow_eq_one p n hn A
  · intro hc
    have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
    have hc' : (c : GaloisField p (2 * n)) ^ (p ^ n + 1) = 1 :=
      congrArg Units.val (show c ^ (p ^ n + 1) = 1 from hc)
    let A : GL (Fin 2) (GaloisField p (2 * n)) :=
      mkOfDetNeZero !![(c : GaloisField p (2 * n)), 0; 0, 1]
        (by simp [Matrix.det_fin_two])
    have hA : A ∈ (unitaryForm 2 p n hn).unitarySubgroup := by
      rw [(unitaryForm 2 p n hn).mem_unitarySubgroup_iff]
      change (unitaryForm 2 p n hn).conjTranspose A.val * 1 * A.val = 1
      rw [mul_one]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [A, unitaryForm, BenderSuzuki.MatrixGroups.HermitianForm.conjTranspose,
          Matrix.mul_apply, Fin.sum_univ_two, iterateFrobenius_def, ← pow_succ, hc', hp0]
    refine ⟨⟨A, hA⟩, ?_⟩
    apply Units.ext
    change A.val.det = (c : GaloisField p (2 * n))
    simp [A, Matrix.det_fin_two]

end ABG

