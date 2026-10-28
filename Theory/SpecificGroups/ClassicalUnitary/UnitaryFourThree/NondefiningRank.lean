module

public import BenderSuzuki.MatrixGroups.Unitary
public import Theory.LinearAlgebra.FiniteProjectiveMatrixGroup
public import Theory.GroupTheory.PrimeRankCubeFree
public import Theory.GroupTheory.QuasithinBasic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Nondefining odd-prime ranks for four-dimensional field-nine unitary groups

The actual projective image of SU has order dividing the order of GL₄(9),
which is `2¹⁵ · 3¹² · 5² · 7 · 13 · 41`. No odd prime other than three
has its cube dividing this number. Lagrange's theorem therefore bounds
the corresponding prime ranks of every projective unitary subgroup by two.
The argument keeps the actual projection to PGL and does not identify SU
with its projective image or recognize either group from its order.

This supplies the nondefining-prime part of Aschbacher–Smith,
Theorem 0.1.2(4), printed p.4 (repeated as Theorem 0.1.1(4), p.482).
The defining-prime rank inside two-locals is a separate obligation.
-/

open Matrix BenderSuzuki.MatrixGroups

namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree

variable {F : Type*} [Field F] [Finite F]

/-- The ordinary general linear order, factored at the primes relevant to rank. -/
public theorem generalLinear_card_of_field_card_nine (hcard : Nat.card F = 9) :
    Nat.card (GL (Fin 4) F) = 2 ^ 15 * 3 ^ 12 * 5 ^ 2 * 7 * 13 * 41 := by
  let := Fintype.ofFinite F
  rw [card_GL_field]
  norm_num [← Nat.card_eq_fintype_card, hcard, Fin.prod_univ_succ]

/-- Quotienting the special unitary subgroup preserves divisibility by the
ambient general linear order. No assertion of equality with that order is made. -/
public theorem projective_card_dvd_generalLinear_order
    (J : HermitianForm 4 F) (hcard : Nat.card F = 9) :
    Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) ∣
      2 ^ 15 * 3 ^ 12 * 5 ^ 2 * 7 * 13 * 41 := by
  rw [← generalLinear_card_of_field_card_nine hcard]
  exact (J.specialSubgroup.card_map_dvd ProjGenLinGroup.mk).trans
    J.specialSubgroup.card_subgroup_dvd_card

private theorem nondefining_prime_cube_not_dvd
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (h3 : p ≠ 3) :
    ¬ p ^ 3 ∣ 2 ^ 15 * 3 ^ 12 * 5 ^ 2 * 7 * 13 * 41 := by
  intro hd
  have hpd := (dvd_pow_self p (by decide : 3 ≠ 0)).trans hd
  have hpv : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 13 ∨ p = 41 := by
    rcases hp.dvd_mul.mp hpd with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · rcases hp.dvd_mul.mp h with h | h
        · rcases hp.dvd_mul.mp h with h | h
          · rcases hp.dvd_mul.mp h with h | h
            · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
                (hp.dvd_of_dvd_pow h))
            · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
                (hp.dvd_of_dvd_pow h)))
          · exact Or.inr (Or.inr (Or.inl
              ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp (hp.dvd_of_dvd_pow h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inl
            ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h)))))
  rcases hpv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ho.not_two_dvd_nat (dvd_refl 2)
  · exact h3 rfl
  all_goals norm_num at hd

/-- Every nondefining odd-prime rank is bounded for the whole projective group. -/
public theorem odd_primeRank_le_two_of_ne_three
    (J : HermitianForm 4 F) (hcard : Nat.card F = 9)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (h3 : p ≠ 3) :
    primeRank p (ProjectiveSpecialUnitaryMatrixGroup J) ≤ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  exact primeRank_le_two_of_cube_not_dvd fun h =>
    nondefining_prime_cube_not_dvd hp ho h3
      (h.trans (projective_card_dvd_generalLinear_order J hcard))

/-- In particular this bounds every two-local, without needing to classify it. -/
public theorem subgroup_odd_primeRank_le_two_of_ne_three
    (J : HermitianForm 4 F) (hcard : Nat.card F = 9)
    (M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (h3 : p ≠ 3) : primeRank p M ≤ 2 :=
  (Theory.GroupTheory.primeRank_le_of_injective p M.subtype M.subtype_injective).trans
    (odd_primeRank_le_two_of_ne_three J hcard hp ho h3)

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
