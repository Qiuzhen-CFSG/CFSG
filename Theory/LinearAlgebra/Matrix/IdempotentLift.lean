module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.NoncommRing

/-!
# Traces of congruent integral idempotents

Two idempotent matrices with the same residue are intertwined by
`P * Q + (1 - P) * (1 - Q)`. Its residue is the identity, so its determinant
is a unit whenever the coefficient map detects units. The intertwiner also
commutes with every matrix commuting with both idempotents. Consequently
their traces, including equivariant traces, agree in the original ring.

This is the elementary idempotent-conjugacy argument over a local ring,
used in lifting permutation summands for the integral Brauer trace theorem.
Unlike a congruence of traces, the conclusion is an exact equality.
-/

public section

namespace Matrix

variable {R k ι : Type*} [CommRing R] [CommRing k] [Nontrivial k]
  [Fintype ι] [DecidableEq ι]

omit [Nontrivial k] in
/-- A matrix whose reduced determinant is nonzero is invertible whenever
the coefficient map detects units. -/
theorem isUnit_of_map_det_ne_zero
    (f : R →+* k) (hf : ∀ r, f r ≠ 0 → IsUnit r)
    (A : Matrix ι ι R) (hA : (f.mapMatrix A).det ≠ 0) : IsUnit A := by
  apply (isUnit_iff_isUnit_det A).mpr
  apply hf
  rwa [f.map_det]

/-- Equal reductions of idempotents give an invertible intertwiner. It
commutes with every common commuting endomorphism. -/
theorem exists_unit_intertwiner_of_idempotent_map_eq
    (f : R →+* k) (hf : ∀ r, f r ≠ 0 → IsUnit r)
    (P Q : Matrix ι ι R) (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hPQ : f.mapMatrix P = f.mapMatrix Q) :
    ∃ U : (Matrix ι ι R)ˣ,
      P * (U : Matrix ι ι R) = (U : Matrix ι ι R) * Q ∧
      ∀ T, Commute T P → Commute T Q → Commute T (U : Matrix ι ι R) := by
  let A := P * Q + (1 - P) * (1 - Q)
  have hmap : f.mapMatrix A = 1 := by
    have hq : IsIdempotentElem (f.mapMatrix Q) := hQ.map f.mapMatrix
    dsimp [A]
    simp only [map_add, map_mul, map_sub, map_one, hPQ]
    rw [hq.eq, hq.one_sub.eq]
    abel
  have hunit : IsUnit A :=
    isUnit_of_map_det_ne_zero f hf A (by rw [hmap, det_one]; exact one_ne_zero)
  refine ⟨hunit.unit, ?_, ?_⟩
  · rw [hunit.unit_spec]
    dsimp [A]
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul,
      ← mul_assoc, hP.eq]
    simp only [mul_assoc, hQ.eq]
    noncomm_ring
  · intro T hTP hTQ
    rw [hunit.unit_spec]
    exact (hTP.mul_right hTQ).add_right
      (((Commute.one_right T).sub_right hTP).mul_right
        ((Commute.one_right T).sub_right hTQ))

/-- Equivariant traces of congruent idempotents agree in the original
coefficient ring, provided the auxiliary matrix commutes with both. -/
theorem trace_mul_eq_of_idempotent_map_eq
    (f : R →+* k) (hf : ∀ r, f r ≠ 0 → IsUnit r)
    (P Q T : Matrix ι ι R) (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hPQ : f.mapMatrix P = f.mapMatrix Q) (hTP : Commute T P)
    (hTQ : Commute T Q) : trace (T * P) = trace (T * Q) := by
  obtain ⟨U, hU, hcomm⟩ :=
    exists_unit_intertwiner_of_idempotent_map_eq f hf P Q hP hQ hPQ
  have hTU := (hcomm T hTP hTQ).eq
  have hconj : (U : Matrix ι ι R) * (T * Q) * (↑U⁻¹ : Matrix ι ι R) = T * P := by
    calc
      _ = T * ((U : Matrix ι ι R) * Q) * (↑U⁻¹ : Matrix ι ι R) := by
        rw [← mul_assoc, ← hTU, mul_assoc]
        simp only [mul_assoc]
      _ = T * (P * (U : Matrix ι ι R)) * (↑U⁻¹ : Matrix ι ι R) := by rw [hU]
      _ = T * P := by simp only [mul_assoc, Units.mul_inv, mul_one]
  rw [← hconj, trace_units_conj]

/-- Ordinary traces of congruent idempotents agree before reduction. -/
theorem trace_eq_of_idempotent_map_eq
    (f : R →+* k) (hf : ∀ r, f r ≠ 0 → IsUnit r)
    (P Q : Matrix ι ι R) (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hPQ : f.mapMatrix P = f.mapMatrix Q) : trace P = trace Q := by
  simpa only [one_mul] using
    trace_mul_eq_of_idempotent_map_eq f hf P Q 1 hP hQ hPQ
      (Commute.one_left P) (Commute.one_left Q)

end Matrix
