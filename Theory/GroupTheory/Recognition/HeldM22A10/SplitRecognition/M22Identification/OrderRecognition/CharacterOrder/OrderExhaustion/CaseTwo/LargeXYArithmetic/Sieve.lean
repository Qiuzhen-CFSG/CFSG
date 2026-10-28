module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.CaseTwo.LargeXYArithmetic.Finite

/-!
# A congruence filter for the integer quadratic solver

Writing the root as `u = 128*k-o` shows that `A*o²-B*o+C` is divisible by
`gcd(16384*A, 128*(B-2*A*o))`. This filters denominator candidates before
square-root calculation and also handles a zero gcd by ordinary integer
remainder. The root-completeness theorem proves that the filter loses nothing.

Source: the modulo-128 restriction congruences in Janko, *A characterization
of the Mathieu simple groups, I*, J. Algebra 9 (1968), Section 7, pp.14–15.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion.LargeXY

/-- Substitute the restriction congruence before computing any square root. -/
@[expose] public def rootsAt (A B C o : ℤ) : List ℤ :=
  if (A*o^2-B*o+C) % (Int.gcd (16384*A) (128*(B-2*A*o)) : ℤ) = 0 then
    roots A B C else []

public theorem mem_rootsAt {A B C o u : ℤ} (h : A*u^2+B*u+C=0)
    (hr : (u+o)%128=0) (hconst : A = 0 → B = 0 → 0 ≤ u ∧ u < 225) :
    u ∈ rootsAt A B C o := by
  obtain ⟨k,hk⟩ := Int.dvd_of_emod_eq_zero hr
  have hu : u = 128*k-o := by omega
  have he : A*o^2-B*o+C = -(16384*A*k^2+128*(B-2*A*o)*k) := by
    rw [hu] at h
    linear_combination h
  have hd : (Int.gcd (16384*A) (128*(B-2*A*o)) : ℤ) ∣ A*o^2-B*o+C := by
    rw [he]
    exact dvd_neg.mpr (dvd_add (dvd_mul_of_dvd_left (Int.gcd_dvd_left _ _) _)
      (dvd_mul_of_dvd_left (Int.gcd_dvd_right _ _) _))
  rw [rootsAt, if_pos (Int.emod_eq_zero_of_dvd hd)]
  exact mem_roots h hconst

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion.LargeXY
