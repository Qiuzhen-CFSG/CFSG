module

public import Theory.GroupTheory.PGroup.UniqueInvolutionClassification
public import Theory.GroupTheory.SpecificGroups.GeneralizedQuaternionAut
public import Theory.GroupTheory.SpecificGroups.QuaternionEightAut
public import Theory.GroupTheory.PResidual.PrimeSet

/-!
# Automorphisms of two-groups with at most one involution

The cyclic/quaternion classification reduces this calculation to cyclic
two-groups, generalized quaternion groups of order greater than eight, and Q₈.
Their automorphism groups are respectively two-groups, two-groups, and a group
of order 24. The trivial group is included in the cyclic alternative.

Sources: Huppert III.8.2 and the standard quaternion automorphism calculation.
This is applied to the determinant kernel in the GL₂ normalizer calculation
of Aschbacher–Smith A.1.26, printed pp.25–26.
-/

namespace IsPGroup
variable {P : Type*} [Group P] [Finite P]

private theorem unique_involution [Nontrivial P] (hP : IsPGroup 2 P)
    (hu : ∀ x y : P, orderOf x = 2 → orderOf y = 2 → x = y) :
    ∃! x : P, orderOf x = 2 := by
  obtain ⟨x, hx⟩ := exists_ne (1 : P)
  have hz : orderOf (x ^ (orderOf x / 2)) = 2 :=
    orderOf_pow_orderOf_div (orderOf_pos x).ne' (hP.dvd_orderOf hx)
  exact ⟨_, hz, fun y hy => hu y _ hy hz⟩

/-- An abelian two-group with at most one involution is cyclic. -/
public theorem isCyclic_of_involutions_eq [IsMulCommutative P] (hP : IsPGroup 2 P)
    (hu : ∀ x y : P, orderOf x = 2 → orderOf y = 2 → x = y) : IsCyclic P := by
  cases subsingleton_or_nontrivial P
  · infer_instance
  · exact hP.isCyclic_of_unique_involution_of_isMulCommutative (unique_involution hP hu)

private theorem pi_two_three (hP : IsPGroup 2 P) : IsPiGroup twoThreePrimes P := by
  rw [IsPiGroup_iff]
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  intro q hq
  rw [hn] at hq
  exact Or.inl ((Nat.prime_dvd_prime_iff_eq q.property Nat.prime_two).mp
    (q.property.dvd_of_dvd_pow hq))

/-- Only the primes two and three divide the automorphism group of a two-group
with at most one involution. The quaternion group of order eight is the sole
case requiring the prime three. -/
public theorem isPiGroup_mulAut_of_involutions_eq (hP : IsPGroup 2 P)
    (hu : ∀ x y : P, orderOf x = 2 → orderOf y = 2 → x = y) :
    IsPiGroup twoThreePrimes (MulAut P) := by
  by_cases hcyc : IsCyclic P
  · let := hcyc
    exact pi_two_three hP.mulAut_of_isCyclic_two
  let : Nontrivial P := Nontrivial.of_not_isCyclic hcyc
  rcases hP.isCyclic_or_quaternion_of_unique_involution (unique_involution hP hu) with
    hc | ⟨n, hn, ⟨e⟩⟩
  · exact (hcyc hc).elim
  have hQ := hP.of_equiv e
  apply IsPiGroup.of_equiv (e := MulAut.congr e)
  by_cases hsmall : n = 3
  · subst n
    change IsPiGroup twoThreePrimes (MulAut (QuaternionGroup 2))
    rw [IsPiGroup_iff, QuaternionGroup.card_mulAut_two]
    intro q hq
    have hd : q.val ∣ 2 ^ 3 * 3 := by norm_num; exact hq
    rcases q.property.dvd_mul.mp hd with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq q.property Nat.prime_two).mp
        (q.property.dvd_of_dvd_pow h))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq q.property Nat.prime_three).mp h)
  · apply pi_two_three
    apply QuaternionGroup.isPGroup_mulAut_of_two_lt _ hQ
    have hh : 2 ^ 2 ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by decide) (by omega)
    norm_num at hh ⊢
    omega
end IsPGroup
