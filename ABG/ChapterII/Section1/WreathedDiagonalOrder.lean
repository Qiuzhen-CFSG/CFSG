module
public import ABG.ChapterII.Section1.WreathedNormalForm

/-!
# Exact order of the wreathed diagonal

For the element `u = s*t` in ABG Chapter II §1 Lemma 2 (article pp.9–10),
the exact order is `2^n`. The commuting generator relations give this power
as an exponent, and uniqueness of normal coordinates excludes all smaller
positive powers. This supplies the diagonal cyclic group used in the center
and outer-element calculations.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

public theorem orderOf_u : orderOf P.u = 2 ^ n := by
  have hc : Commute P.s P.t := P.commute
  apply (orderOf_eq_iff (by positivity)).mpr
  refine ⟨?_, ?_⟩
  · simp [u, hc.mul_pow, P.s_pow, P.t_pow]
  · intro m hm hpos heq
    have hcoords : P.s ^ (m : ℤ) * P.t ^ (m : ℤ) * P.z ^ (0 : ℤ) =
        P.s ^ (0 : ℤ) * P.t ^ (0 : ℤ) * P.z ^ (0 : ℤ) := by
      simpa [u, hc.mul_pow] using heq
    have h := ((P.normal_form_zpow_eq_iff m m 0 0 0 0).mp hcoords).1
    have hm' : (m : ℤ) < (2 ^ n : ℕ) := by exact_mod_cast hm
    rw [Int.emod_eq_of_lt (by omega) hm', Int.zero_emod] at h
    omega
end ABG.Wreathed.Presentation
