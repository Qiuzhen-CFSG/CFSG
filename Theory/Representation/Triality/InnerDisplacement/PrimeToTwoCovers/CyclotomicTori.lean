module

public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.Arithmetic
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.SevenAtTwo
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiThree
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiSix
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiTwelve

/-!
# Cyclotomic primes in binary triality central covers

At q = 2, the explicit order-49 torus and its determinant-four conjugator
settle seven, while the proved Bruhat count settles thirteen. Hence every
prime greater than three is excluded from every finite perfect central
cover at this parameter, including the literal map R → R/Z(R).

For larger q, the proved Bruhat order reduces the calculation to the third,
sixth and twelfth cyclotomic factors. `PhiThree` and `PhiSix` construct actual
Sylow torus pairs whose ambient conjugators act by q² and 1, detecting the
lifted alternating pairing. `PhiTwelve` constructs a cyclic torus containing
the full primary subgroup, including repeated primes. These constructions
discharge all three premises of the retained conditional assembly below.

Thus every prime p > 3 not dividing q²−1 is excluded from every finite
perfect central kernel. The final center theorem applies this to the
literal projection R → R/Z(R), for every positive binary exponent.

Source: GLS3 §6.1, Theorem 6.1.4 and Tables 6.1.2–3, with the graph-field
and central-quotient conventions of §2.2. The tables motivate the target
but are not proof inputs.
-/

public section

namespace Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori
open PerfectCentralCovering PerfectCentralCovering.OddSylow

/-- All primes greater than three dividing the smallest carrier have local geometry. -/
theorem geometry_at_two {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hcard : p ∣ Nat.card (Standard.BinaryCarrier 1 Nat.zero_lt_one)) :
    Geometry p (Standard.BinaryCarrier 1 Nat.zero_lt_one) := by
  have hp' := (Fact.out : p.Prime)
  have h3 : ¬ p ∣ 3 := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq hp' Nat.prime_three).mp h
    omega
  have hquad : ¬ p ∣ (2 ^ 1) ^ 2 - 1 := by norm_num; exact h3
  have h := dvd_cyclotomic_of_dvd_card Nat.zero_lt_one hp hquad hcard
  norm_num at h
  rcases h with h7 | h3' | h13
  · have heq : p = 7 := (Nat.prime_dvd_prime_iff_eq hp' (by norm_num)).mp h7
    subst p
    exact SevenAtTwo.geometry
  · exact (h3 h3').elim
  · have heq : p = 13 := (Nat.prime_dvd_prime_iff_eq hp' (by norm_num)).mp h13
    subst p
    exact thirteen_geometry_at_two

/-- Unconditional prime exclusion at q = 2 for every finite perfect central cover. -/
theorem not_dvd_card_kernel_at_two {E : Type*} [Group E] [Finite E]
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (f : Cover E (Standard.BinaryCarrier 1 Nat.zero_lt_one)) :
    ¬ p ∣ Nat.card f.toMonoidHom.ker := by
  have h : Geometry p (Standard.BinaryCarrier 1 Nat.zero_lt_one) := by
    by_cases hc : p ∣ Nat.card (Standard.BinaryCarrier 1 Nat.zero_lt_one)
    · exact geometry_at_two hp hc
    · exact geometry_of_not_dvd_card hc
  exact h.not_dvd_card_kernel (by omega) f

/-- Application to the original central projection at q = 2. -/
theorem not_dvd_card_center_at_two {R : Type*} [Group R] [Finite R]
    [Group.IsPerfect R] {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hmodel : Standard.IsTrialityGroupAt 2 (R ⧸ Subgroup.center R)) :
    ¬ p ∣ Nat.card (Subgroup.center R) := by
  obtain ⟨e⟩ := (Standard.isTrialityGroupAt_two_iff _).mp hmodel
  rw [← centralQuotientCover_ker e]
  exact not_dvd_card_kernel_at_two hp (centralQuotientCover e)

/-- Conditional assembly; only larger-parameter geometric witnesses remain. -/
theorem geometry_of_remaining_tori (n : ℕ) (hn : 0 < n)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hquad : ¬ p ∣ (2 ^ n) ^ 2 - 1)
    (hcard : p ∣ Nat.card (Standard.BinaryCarrier n hn))
    (hthree : 1 < n → p ∣ (2 ^ n) ^ 2 + 2 ^ n + 1 →
      ∃ Q : Sylow p (Standard.BinaryCarrier n hn), Nonempty (TorusPair (Q : Subgroup (Standard.BinaryCarrier n hn))))
    (hsix : 1 < n → p ∣ (2 ^ n) ^ 2 - 2 ^ n + 1 →
      ∃ Q : Sylow p (Standard.BinaryCarrier n hn), Nonempty (TorusPair (Q : Subgroup (Standard.BinaryCarrier n hn))))
    (htwelve : 1 < n → p ^ 2 ∣ (2 ^ n) ^ 4 - (2 ^ n) ^ 2 + 1 →
      ∀ Q : Sylow p (Standard.BinaryCarrier n hn), IsCyclic Q) :
    Geometry p (Standard.BinaryCarrier n hn) := by
  by_cases hsmall : n = 1
  · subst n
    exact geometry_at_two hp hcard
  have hlarge : 1 < n := by omega
  rcases dvd_cyclotomic_of_dvd_card hn hp hquad hcard with h3 | h6 | h12
  · obtain ⟨Q, ⟨d⟩⟩ := hthree hlarge h3
    exact .torus Q d
  · obtain ⟨Q, ⟨d⟩⟩ := hsix hlarge h6
    exact .torus Q d
  · by_cases hsq : p ^ 2 ∣ (2 ^ n) ^ 4 - (2 ^ n) ^ 2 + 1
    · exact .cyclic (htwelve hlarge hsq)
    · exact geometry_of_phi12_multiplicity_one hn (by omega) h12 hsq

/-- The concrete remaining witnesses imply the requested kernel exclusion. -/
theorem not_dvd_card_kernel_of_remaining_tori {E : Type*} [Group E] [Finite E]
    (n : ℕ) (hn : 0 < n) {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hquad : ¬ p ∣ (2 ^ n) ^ 2 - 1)
    (hcard : p ∣ Nat.card (Standard.BinaryCarrier n hn))
    (hthree : 1 < n → p ∣ (2 ^ n) ^ 2 + 2 ^ n + 1 →
      ∃ Q : Sylow p (Standard.BinaryCarrier n hn), Nonempty (TorusPair (Q : Subgroup (Standard.BinaryCarrier n hn))))
    (hsix : 1 < n → p ∣ (2 ^ n) ^ 2 - 2 ^ n + 1 →
      ∃ Q : Sylow p (Standard.BinaryCarrier n hn), Nonempty (TorusPair (Q : Subgroup (Standard.BinaryCarrier n hn))))
    (htwelve : 1 < n → p ^ 2 ∣ (2 ^ n) ^ 4 - (2 ^ n) ^ 2 + 1 →
      ∀ Q : Sylow p (Standard.BinaryCarrier n hn), IsCyclic Q)
    (f : Cover E (Standard.BinaryCarrier n hn)) :
    ¬ p ∣ Nat.card f.toMonoidHom.ker :=
  (geometry_of_remaining_tori n hn hp hquad hcard hthree hsix htwelve).not_dvd_card_kernel
    (by omega) f

/-- The same conditional calculation on the literal map R → R/Z(R). -/
theorem not_dvd_card_center_of_remaining_tori {R : Type*} [Group R] [Finite R]
    [Group.IsPerfect R] (n : ℕ) (hn : 0 < n)
    (hmodel : Standard.IsTrialityGroupAt (2 ^ n) (R ⧸ Subgroup.center R))
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hquad : ¬ p ∣ (2 ^ n) ^ 2 - 1)
    (hcard : p ∣ Nat.card (Standard.BinaryCarrier n hn))
    (hthree : 1 < n → p ∣ (2 ^ n) ^ 2 + 2 ^ n + 1 →
      ∃ Q : Sylow p (Standard.BinaryCarrier n hn), Nonempty (TorusPair (Q : Subgroup (Standard.BinaryCarrier n hn))))
    (hsix : 1 < n → p ∣ (2 ^ n) ^ 2 - 2 ^ n + 1 →
      ∃ Q : Sylow p (Standard.BinaryCarrier n hn), Nonempty (TorusPair (Q : Subgroup (Standard.BinaryCarrier n hn))))
    (htwelve : 1 < n → p ^ 2 ∣ (2 ^ n) ^ 4 - (2 ^ n) ^ 2 + 1 →
      ∀ Q : Sylow p (Standard.BinaryCarrier n hn), IsCyclic Q) :
    ¬ p ∣ Nat.card (Subgroup.center R) := by
  obtain ⟨e⟩ := (Standard.isTrialityGroupAt_binary_iff _ n hn).mp hmodel
  rw [← centralQuotientCover_ker e]
  exact not_dvd_card_kernel_of_remaining_tori n hn hp hquad hcard hthree hsix htwelve
    (centralQuotientCover e)

/-- Every prime greater than three outside q²−1 that divides the actual
carrier order has local Sylow geometry. All three torus constructions are
supplied, including full primary multiplicities and the parameter n = 1. -/
theorem geometry (n : ℕ) (hn : 0 < n) {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hquad : ¬ p ∣ (2 ^ n) ^ 2 - 1)
    (hcard : p ∣ Nat.card (Standard.BinaryCarrier n hn)) :
    Geometry p (Standard.BinaryCarrier n hn) :=
  geometry_of_remaining_tori n hn hp hquad hcard
    (fun hlarge hthree => PhiThree.exists_sylow_pair n hn hlarge hp hthree)
    (fun hlarge hsix => PhiSix.exists_sylow_pair hn hlarge hp hsix)
    (fun hlarge htwelve => PhiTwelve.isCyclic_sylow_of_square_dvd n hn hlarge hp htwelve)

/-- Cyclotomic prime exclusion for every finite perfect central cover of the
genuine binary triality group. Primes outside the carrier order are also
excluded, so no divisibility assumption on that order is needed. -/
theorem not_dvd_card_kernel {E : Type*} [Group E] [Finite E]
    (n : ℕ) (hn : 0 < n) {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hquad : ¬ p ∣ (2 ^ n) ^ 2 - 1)
    (f : Cover E (Standard.BinaryCarrier n hn)) :
    ¬ p ∣ Nat.card f.toMonoidHom.ker := by
  have h : Geometry p (Standard.BinaryCarrier n hn) := by
    by_cases hcard : p ∣ Nat.card (Standard.BinaryCarrier n hn)
    · exact geometry n hn hp hquad hcard
    · exact geometry_of_not_dvd_card hcard
  exact h.not_dvd_card_kernel (by omega) f

/-- The same exclusion for the literal central quotient of the original
finite perfect group, with no remaining geometric premise. -/
theorem not_dvd_card_center {R : Type*} [Group R] [Finite R] [Group.IsPerfect R]
    (n : ℕ) (hn : 0 < n)
    (hmodel : Standard.IsTrialityGroupAt (2 ^ n) (R ⧸ Subgroup.center R))
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hquad : ¬ p ∣ (2 ^ n) ^ 2 - 1) :
    ¬ p ∣ Nat.card (Subgroup.center R) := by
  obtain ⟨e⟩ := (Standard.isTrialityGroupAt_binary_iff _ n hn).mp hmodel
  rw [← centralQuotientCover_ker e]
  exact not_dvd_card_kernel n hn hp hquad (centralQuotientCover e)

end Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori
