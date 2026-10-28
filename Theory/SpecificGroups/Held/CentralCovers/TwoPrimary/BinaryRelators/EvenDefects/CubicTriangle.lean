module

public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Algebra.Group.Conj

/-!
# Comparing central square defects in a cubic triangle

If `a² = d`, `(ba)² = c`, and `b³` are central elements of exponent dividing
two, then `c = d`. Conjugation by `a` inverts `b` up to the central factor
`cd`; taking third powers forces that factor to be trivial.

This is the elementary comparison step for the square and sixth-power defects
in John Bray's ATLAS Held presentation, retained in `Held/Model/Source/HeG1-P1.M`.
It does not construct the required word `b` or assert that either Held defect
vanishes. The source-word certificate must discharge all its hypotheses.
-/

namespace Held.CentralCovers.TwoPrimary.BinaryRelators.EvenDefects

/-- The two central square defects in a cubic triangle agree. -/
public theorem cubic_triangle {E : Type*} [Group E] (a b c d : E)
    (hc : c ∈ Subgroup.center E) (hd : d ∈ Subgroup.center E)
    (hc2 : c ^ 2 = 1) (hd2 : d ^ 2 = 1)
    (ha : a ^ 2 = d) (hba : (b * a) ^ 2 = c)
    (hb3 : b ^ 3 ∈ Subgroup.center E) (hb6 : b ^ 6 = 1) : c = d := by
  have hdmove (g : E) : d * g = g * d := (Subgroup.mem_center_iff.mp hd g).symm
  have hai : a⁻¹ = a * d := inv_eq_of_mul_eq_one_right (by
    calc
      a * (a * d) = a ^ 2 * d := by simp only [pow_two, mul_assoc]
      _ = 1 := by rw [ha, ← pow_two, hd2])
  have hab : a⁻¹ * b * a = b⁻¹ * (c * d) := by
    calc
      a⁻¹ * b * a = a * b * a * d := by rw [hai]; simp only [mul_assoc, hdmove]
      _ = b⁻¹ * ((b * a) ^ 2 * d) := by simp only [pow_two, mul_assoc, inv_mul_cancel_left]
      _ = b⁻¹ * (c * d) := by rw [hba]
  have hcd : c * d ∈ Subgroup.center E := Subgroup.mul_mem _ hc hd
  have hcd2 : (c * d) ^ 2 = 1 := by
    rw [(show Commute c d from Subgroup.mem_center_iff.mp hd c).mul_pow, hc2, hd2,
      mul_one]
  have hcd3 : (c * d) ^ 3 = c * d := by
    rw [show 3 = 2 + 1 from rfl, pow_add, hcd2, pow_one, one_mul]
  have hb3inv : (b ^ 3)⁻¹ = b ^ 3 := inv_eq_of_mul_eq_one_right (by
    rw [← pow_add]; exact hb6)
  have hp : b ^ 3 = b ^ 3 * (c * d) := by
    calc
      b ^ 3 = a⁻¹ * b ^ 3 * a := by
        rw [Subgroup.mem_center_iff.mp hb3 a⁻¹, mul_assoc, inv_mul_cancel, mul_one]
      _ = (a⁻¹ * b * a) ^ 3 := by
        simpa only [inv_inv] using (conj_pow (a := a⁻¹) (b := b) (i := 3)).symm
      _ = (b⁻¹ * (c * d)) ^ 3 := by rw [hab]
      _ = b ^ 3 * (c * d) := by
        rw [(show Commute b⁻¹ (c * d) from Subgroup.mem_center_iff.mp hcd b⁻¹).mul_pow,
          inv_pow, hb3inv, hcd3]
  have he : c * d = 1 := mul_left_cancel (hp.symm.trans (mul_one _).symm)
  calc
    c = (c * d) * d := by rw [mul_assoc, ← pow_two, hd2, mul_one]
    _ = d := by rw [he, one_mul]

end Held.CentralCovers.TwoPrimary.BinaryRelators.EvenDefects
