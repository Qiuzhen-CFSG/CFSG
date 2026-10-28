module
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.PCoreLocalSetup
/-!
# Odd primes in the residual of a two-core quotient

Factoring out a normal two-core does not remove an odd prime divisor of the
group order. Taking the two-residual does not remove it either, because the
remaining quotient is a two-group. Both claims follow from the literal
subgroup cardinality products. Source application: Aschbacher--Smith E.2.1
and the cubic specialization in 13.2.9, printed pp.215 and 880--881.
-/
public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
private theorem not_dvd_twoGroup_card {X : Type*} [Group X] [Finite X] {r : ℕ} (hr : r.Prime) (ho : Odd r) (hX : IsPGroup 2 X) : ¬ r ∣ Nat.card X := by
  obtain ⟨n,hn⟩ := hX.exists_card_eq
  rw [hn]
  intro hh
  have he : r = 2 := (Nat.dvd_prime Nat.prime_two).mp (hr.dvd_of_dvd_pow hh) |>.resolve_left hr.ne_one
  subst r
  exact (by decide : ¬ Odd 2) ho

/-- Odd-prime divisors survive passage first through the two-core quotient
and then to its two-residual. -/
theorem odd_prime_dvd_twoCore_quotient_residual {r : ℕ} (hr : r.Prime) (ho : Odd r)
    (hd : r ∣ Nat.card G) : r ∣ Nat.card (pResidual 2 (G ⧸ pCore 2 G)) := by
  have hquot : r ∣ Nat.card (G ⧸ pCore 2 G) := by
    have he := (pCore 2 G).card_mul_index
    rw [← he] at hd
    exact (hr.dvd_mul.mp hd).resolve_left (not_dvd_twoGroup_card hr ho (pCore_isPGroup (p := 2) (G := G)))
  have he := (pResidual 2 (G ⧸ pCore 2 G)).card_mul_index
  rw [← he] at hquot
  exact (hr.dvd_mul.mp hquot).resolve_right (not_dvd_twoGroup_card hr ho (isPGroup_quotient_pResidual 2 (G := G ⧸ pCore 2 G)))
end Theory.GroupTheory
