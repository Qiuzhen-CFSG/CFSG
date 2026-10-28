module

public import Mathlib.GroupTheory.Sylow

/-!
# Normal Sylow three-subgroups from an odd-prime normal subgroup

Let a finite group have a normal `p`-subgroup `R`, for a prime `p ≠ 2`,
and suppose its quotient by `R` is a 2-group. If three divides the group
order, every supplied Sylow three-subgroup is normal. The quotient uses
the same normality instance supplied for `R`.

The subgroup-quotient cardinality formula forces three to divide `|R|`,
and hence `p = 3`. The quotient has order prime to three, so `R` is itself
a Sylow three-subgroup. Normal Sylow uniqueness gives the result for the
supplied Sylow subgroup. The assumption `p ≠ 2` is retained for the
odd-prime interface; the divisibility argument already forces `p = 3`.

Source: elementary Sylow theory and the subgroup-quotient cardinality
formula. This is the standalone normality step used in the Sylow-three
Frattini argument in Stellmacher (4.6).
-/

namespace Subgroup

/-- A normal odd-prime subgroup with 2-group quotient forces normal Sylow three
when three divides the ambient order. -/
public theorem sylow_three_normal_of_odd_prime_normal_quotient_two
    {G : Type*} [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (_hp2 : p ≠ 2)
    (R : Subgroup G) [R.Normal]
    (hR : IsPGroup p R) (hquot : IsPGroup 2 (G ⧸ R))
    (hthree : 3 ∣ Nat.card G) (T : Sylow 3 G) :
    (T : Subgroup G).Normal := by
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := hR.exists_card_eq
  obtain ⟨m, hm⟩ := hquot.exists_card_eq
  have hnotQ : ¬ 3 ∣ Nat.card (G ⧸ R) := by
    rw [hm]
    intro hd
    have hdiv := Nat.prime_three.dvd_of_dvd_pow hd
    norm_num at hdiv
  have hthreeR : 3 ∣ Nat.card R := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup R] at hthree
    exact (Nat.prime_three.dvd_mul.mp hthree).resolve_left hnotQ
  have hp3 : p = 3 := by
    rw [hn] at hthreeR
    have hdiv := Nat.prime_three.dvd_of_dvd_pow hthreeR
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hdiv).symm
  subst p
  have hindex : ¬ 3 ∣ R.index := by
    rwa [Subgroup.index_eq_card]
  let U : Sylow 3 G := hR.toSylow hindex
  have hU : U.Normal := (inferInstance : R.Normal)
  let _ : Unique (Sylow 3 G) := Sylow.unique_of_normal U hU
  exact Sylow.normal_of_subsingleton T

end Subgroup
