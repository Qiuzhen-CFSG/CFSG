module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Setup

/-!
# Odd-product witnesses for fusion to the standard involution

For a candidate involution `y`, choose a short ambient word `r` such that
`y * (r * generatorA * r⁻¹)` has an odd power equal to one. The usual dihedral
identity constructs a conjugator from `y` to `generatorA`; neither its exact
order nor the order of the ambient group is needed.

This specializes the elementary odd-product argument used in
`Theory/GroupTheory/ZStar/OddProductConjugator.lean`, replacing the element-order
hypothesis with the finite power identity supplied by `Two/source/Generate.py`.
-/

namespace ONan.Simplicity.TwoCertificate
/-- A checked odd-power identity supplies the required involution fusion. -/
public theorem generatorA_eq_conj_of_odd_power (y r : Model) (k : ℕ) (hy : y ^ 2 = 1)
    (h : (y * (r * generatorA * r⁻¹)) ^ (2 * k + 1) = 1) :
    ∃ g : Model, generatorA = g * y * g⁻¹ := by
  let t := r * generatorA * r⁻¹
  have ht : t * t = 1 := by
    have hp := congrArg (MulAut.conj r) generatorA_pow_two
    simpa [MulAut.conj_apply, map_pow, pow_two, t] using hp
  have hy' : y * y = 1 := by simpa only [pow_two] using hy
  have hsem : SemiconjBy t (y * t)⁻¹ (y * t) := by
    change t * (y * t)⁻¹ = (y * t) * t
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ht,
      inv_eq_of_mul_eq_one_right hy']
    rw [← mul_assoc, ht, one_mul, mul_assoc, ht, mul_one]
  let q := (y * t) ^ (k + 1)
  have hq : q * t * q⁻¹ = y := by
    change (y * t) ^ (k + 1) * t * ((y * t) ^ (k + 1))⁻¹ = y
    calc
      _ = (y * t) ^ (k + 1) * ((y * t) ^ (k + 1) * t) := by
        rw [← inv_pow, mul_assoc, (hsem.pow_right (k + 1)).eq]
      _ = (y * t) ^ ((2 * k + 1) + 1) * t := by
        rw [← mul_assoc, ← pow_add]
        congr 2
        omega
      _ = y := by rw [pow_succ, h, one_mul, mul_assoc, ht, mul_one]
  refine ⟨r⁻¹ * q⁻¹, ?_⟩
  rw [← hq]
  simp [t, mul_assoc]
end ONan.Simplicity.TwoCertificate
