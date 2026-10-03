module
public import ABG.ChapterII.Section2.UnitaryDeterminantModels
public import Theory.SpecificGroups.GL2.DiagonalSwap

/-!
# The actual unitary diagonal-and-swap subgroup

If a unit ζ satisfies ζ^(2^r)=1, r is nonzero, and 2^r divides p^n+1,
then the shared diagonal-and-swap subgroup over GF(p^(2n)) lies in both
the original GU2 and the actual GL2 determinant level r. Restricting this
subgroup to GU2 therefore places it in the original SU2Level r.

The divisor hypothesis makes ζ norm one. Each diagonal generator preserves
the stored identity-Gram q-Frobenius Hermitian form, and the coordinate
swap preserves it directly. Their determinants are ζ, ζ and -1. The
first two have the required power by hypothesis, while the last does
because 2^r is even. Closure of these original matrix generators then
lies in the intersection. Neither primitivity nor odd characteristic is
needed for this containment statement.

Source: ABG II.2 Lemma 1(i), article page 17. This is the matrix-containment
prerequisite of the actual unitary wreathed Sylow model; presentation,
cardinality and Sylow maximality are supplied by its other prerequisites.
-/

namespace ABG
open Matrix.GeneralLinearGroup

private theorem diagonalPair_mem_unitary
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0)
    (a b : (GaloisField p (2 * n))ˣ)
    (ha : a ^ (p ^ n + 1) = 1) (hb : b ^ (p ^ n + 1) = 1) :
    diagonalPair (GaloisField p (2 * n)) (a, b) ∈
      (unitaryForm 2 p n hn).unitarySubgroup := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have ha' := congrArg Units.val ha
  have hb' := congrArg Units.val hb
  rw [(unitaryForm 2 p n hn).mem_unitarySubgroup_iff]
  change (unitaryForm 2 p n hn).conjTranspose _ * 1 * _ = 1
  rw [mul_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalPair, unitaryForm, BenderSuzuki.MatrixGroups.HermitianForm.conjTranspose,
      Matrix.mul_apply, Fin.sum_univ_two, iterateFrobenius_def, ← pow_succ, hp0,
      show (a : GaloisField p (2 * n)) ^ (p ^ n + 1) = 1 from ha',
      show (b : GaloisField p (2 * n)) ^ (p ^ n + 1) = 1 from hb']

public theorem diagonalSwapSubgroup_le_unitaryDeterminant
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) (r : ℕ) (hr : r ≠ 0)
    (hd : 2 ^ r ∣ p ^ n + 1) (ζ : (GaloisField p (2 * n))ˣ)
    (hζ : ζ ^ (2 ^ r) = 1) :
    diagonalSwapSubgroup (GaloisField p (2 * n)) ζ ≤
      (unitaryForm 2 p n hn).unitarySubgroup ⊓
        determinantTwoPower (GaloisField p (2 * n)) r := by
  let F := GaloisField p (2 * n)
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hnorm : ζ ^ (p ^ n + 1) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_iff_pow_eq_one.mpr hζ).trans hd)
  have hζ' : (ζ : F) ^ (2 ^ r) = 1 := congrArg Units.val hζ
  have heven : Even (2 ^ r) := even_two.pow_of_ne_zero hr
  rw [diagonalSwapSubgroup, Subgroup.closure_le]
  intro A hA
  rcases (by simpa using hA : A = diagonalPair F (ζ,1) ∨
    A = diagonalPair F (1,ζ) ∨ A = coordinateSwap F) with rfl | rfl | rfl
  · refine ⟨diagonalPair_mem_unitary p n hn ζ 1 hnorm (one_pow _), ?_⟩
    change det (diagonalPair F (ζ,1)) ^ (2 ^ r) = 1
    apply Units.ext
    change (diagonalPair F (ζ,1)).val.det ^ (2 ^ r) = 1
    simp [diagonalPair_val, Matrix.det_fin_two, hζ']
  · refine ⟨diagonalPair_mem_unitary p n hn 1 ζ (one_pow _) hnorm, ?_⟩
    change det (diagonalPair F (1,ζ)) ^ (2 ^ r) = 1
    apply Units.ext
    change (diagonalPair F (1,ζ)).val.det ^ (2 ^ r) = 1
    simp [diagonalPair_val, Matrix.det_fin_two, hζ']
  · constructor
    · change coordinateSwap F ∈ (unitaryForm 2 p n hn).unitarySubgroup
      rw [(unitaryForm 2 p n hn).mem_unitarySubgroup_iff]
      change (unitaryForm 2 p n hn).conjTranspose _ * 1 * _ = 1
      rw [mul_one]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [coordinateSwap, unitaryForm, BenderSuzuki.MatrixGroups.HermitianForm.conjTranspose,
          Matrix.mul_apply, Fin.sum_univ_two, iterateFrobenius_def, hp0]
    · change det (coordinateSwap F) ^ (2 ^ r) = 1
      apply Units.ext
      change (coordinateSwap F).val.det ^ (2 ^ r) = 1
      simpa [coordinateSwap_val, Matrix.det_fin_two] using
        (heven.neg_one_pow : (-1 : F) ^ (2 ^ r) = 1)

end ABG

