module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Tactic

/-!
# Odd prime divisors of the binary degree-five linear group

The factorization of |GL₅(2)| excludes every odd prime cube. These two
arithmetic facts are shared by the ordinary and covering model inspections
for the original normal A₆ upper component in Aschbacher–Smith 13.3.2,
printed pp.884–885.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.OrderArithmetic

theorem odd_prime_dvd_gl_five {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hd : p ∣ 9999360) : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 31 := by
  have hfac : 9999360 = 2 ^ 10 * 3 ^ 2 * 5 * 7 * 31 := by norm_num
  rw [hfac] at hd
  have heq (q : ℕ) (hq : q.Prime) (h : p ∣ q) : p = q :=
    ((Nat.dvd_prime hq).mp h).resolve_left hp.ne_one
  rcases hp.dvd_mul.mp hd with hd | hd
  · rcases hp.dvd_mul.mp hd with hd | hd
    · rcases hp.dvd_mul.mp hd with hd | hd
      · rcases hp.dvd_mul.mp hd with hd | hd
        · have he := heq 2 (by decide) (hp.dvd_of_dvd_pow hd)
          subst p
          norm_num at ho
        · exact Or.inl (heq 3 (by decide) (hp.dvd_of_dvd_pow hd))
      · exact Or.inr (Or.inl (heq 5 (by decide) hd))
    · exact Or.inr (Or.inr (Or.inl (heq 7 (by decide) hd)))
  · exact Or.inr (Or.inr (Or.inr (heq 31 (by decide) hd)))

theorem odd_cube_not_dvd_gl_five {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    ¬ p ^ 3 ∣ 9999360 := by
  intro hd
  have hd₀ : p ∣ 9999360 := (dvd_pow_self p (by decide : 3 ≠ 0)).trans hd
  rcases odd_prime_dvd_gl_five hp ho hd₀ with rfl | rfl | rfl | rfl <;> norm_num at hd

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.OrderArithmetic
