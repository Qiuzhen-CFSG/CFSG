module

public import Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic.Diagonal

/-!
# Full Sylow subgroups as norm-one parameters

For an odd prime r dividing p+1, r is coprime to p−1. Thus a Sylow
r-subgroup of the units of a field of order p² has order dividing p+1.
Every element has norm one for the p-power involution, and the subgroup
has odd order. No restriction is placed on the r-valuation of p+1.

The concrete application is the rank-three diagonal torus in PSU₄. These
parameters supply its entire r-part for the covering-kernel argument in
Aschbacher–Smith A.2.17, printed p.39, and I.1.1–I.1.4, printed pp.407–408.
-/

public section
open Matrix Subgroup BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
namespace Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic
variable {F : Type*} [Field F] [Finite F]
variable {p r : ℕ} [Fact p.Prime] [Fact r.Prime]

private theorem prime_coprime_predecessor (hr2 : r ≠ 2) (hd : r ∣ p + 1) :
    r.Coprime (p - 1) := by
  apply (Fact.out : r.Prime).coprime_iff_not_dvd.mpr
  intro he
  have hp := (Fact.out : p.Prime).two_le
  have ht : r ∣ 2 := by
    convert Nat.dvd_sub hd he using 1
    omega
  exact hr2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : r.Prime) Nat.prime_two).mp ht)

/-- The entire Sylow subgroup order divides p+1, including all higher prime powers. -/
theorem sylow_units_card_dvd_succ (hr2 : r ≠ 2) (hd : r ∣ p + 1)
    (hF : Nat.card F = p ^ 2) (P : Sylow r Fˣ) : Nat.card P ∣ p + 1 := by
  have hc : (Nat.card P).Coprime (p - 1) := by
    rw [P.card_eq_multiplicity]
    exact (prime_coprime_predecessor hr2 hd).pow_left _
  apply hc.dvd_of_dvd_mul_left
  have he := P.toSubgroup.card_subgroup_dvd_card
  rw [Nat.card_units, hF] at he
  have heq : p ^ 2 - 1 = (p + 1) * (p - 1) := by
    simpa only [one_pow, mul_comm] using Nat.sq_sub_sq p 1
  simpa only [heq, mul_comm] using he

/-- Every Sylow parameter has norm one under the prescribed field involution. -/
theorem sylow_units_norm (J : HermitianForm 4 F) (hr2 : r ≠ 2) (hd : r ∣ p + 1)
    (hF : Nat.card F = p ^ 2) (hconj : ∀ x, J.conj x = x ^ p) (P : Sylow r Fˣ)
    (u : P) : J.conj (u.val : F) * (u.val : F) = 1 := by
  rw [hconj, ← pow_succ]
  have he : u ^ (p + 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp
    ((orderOf_dvd_natCard u).trans (sylow_units_card_dvd_succ hr2 hd hF P))
  exact congrArg (fun v : P => (v.val : F)) he

/-- An odd-prime Sylow parameter group has odd order. -/
theorem sylow_units_card_coprime_two (hr2 : r ≠ 2) (P : Sylow r Fˣ) :
    (Nat.card P).Coprime 2 := by
  rw [P.card_eq_multiplicity]
  exact ((Fact.out : r.Prime).coprime_iff_not_dvd.mpr (fun h =>
    hr2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : r.Prime) Nat.prime_two).mp h))).pow_left _

end Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic
