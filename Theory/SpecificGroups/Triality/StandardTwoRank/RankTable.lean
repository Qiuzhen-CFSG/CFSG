module

public import Theory.SpecificGroups.Triality.StandardTwoRank.Automorphisms.Unconditional

/-!
# Triality ranks for every standard parameter and model witness

Uniqueness of prime-power parameters identifies every standard parameter of
field order 2^n with `binaryParameters n hn`. An `IsTrialityGroupAt` witness
then supplies an actual carrier equivalence. Its restriction to the derived
subgroup and conjugation of automorphisms transport the unconditional rank
table, without a simplicity, perfectness or rank premise on the source group.

Source: Aschbacher–Smith, printed p.356, 16.1.7(3a) on p.1172 and the
doubled-rank comparison in 16.3.9 on p.1180 (`refs/quasithin.pdf`).
-/

public section
noncomputable section

namespace Triality.Standard.TwoRank
open Theory.GroupTheory

/-- The exact intrinsic rank for arbitrary genuine parameters at field order 2^n. -/
theorem twoRank_eq_five_mul_of_parameters (n : ℕ) (hn : 0 < n)
    (P : Parameters) (hq : P.q = 2 ^ n) : primeRank 2 (Carrier P) = 5 * n := by
  rw [P.eq_binaryParameters_of_q_eq n hn hq]
  exact twoRank_eq_five_mul n hn

/-- The requested lower bound on every standard carrier. -/
theorem twoRank_ge_five_mul_of_parameters (n : ℕ) (hn : 0 < n)
    (P : Parameters) (hq : P.q = 2 ^ n) : 5 * n ≤ primeRank 2 (Carrier P) :=
  (twoRank_eq_five_mul_of_parameters n hn P hq).ge

/-- The exact derived rank for arbitrary genuine parameters. -/
theorem derived_twoRank_eq_five_mul_of_parameters (n : ℕ) (hn : 0 < n)
    (P : Parameters) (hq : P.q = 2 ^ n) :
    primeRank 2 (commutator (Carrier P)) = 5 * n := by
  rw [P.eq_binaryParameters_of_q_eq n hn hq]
  exact derived_twoRank_eq_five_mul n hn

/-- The exact automorphism rank for arbitrary genuine parameters. -/
theorem automorphism_twoRank_eq_five_mul_of_parameters (n : ℕ) (hn : 0 < n)
    (P : Parameters) (hq : P.q = 2 ^ n) :
    primeRank 2 (MulAut (Carrier P)) = 5 * n := by
  rw [P.eq_binaryParameters_of_q_eq n hn hq]
  exact automorphism_twoRank_eq_five_mul n hn

/-- The exact derived-automorphism rank for arbitrary genuine parameters. -/
theorem derived_automorphism_twoRank_eq_five_mul_of_parameters (n : ℕ) (hn : 0 < n)
    (P : Parameters) (hq : P.q = 2 ^ n) :
    primeRank 2 (MulAut (commutator (Carrier P))) = 5 * n := by
  rw [P.eq_binaryParameters_of_q_eq n hn hq]
  exact derived_automorphism_twoRank_eq_five_mul n hn

/-- The requested automorphism upper bound for every standard derived carrier. -/
theorem derived_automorphism_twoRank_le_five_mul_of_parameters (n : ℕ) (hn : 0 < n)
    (P : Parameters) (hq : P.q = 2 ^ n) :
    primeRank 2 (MulAut (commutator (Carrier P))) ≤ 5 * n :=
  (derived_automorphism_twoRank_eq_five_mul_of_parameters n hn P hq).le

/-- Intrinsic rank transports through every actual triality-model witness. -/
theorem twoRank_eq_five_mul_of_model (n : ℕ) (hn : 0 < n)
    {G : Type*} [Group G] (hG : IsTrialityGroupAt (2 ^ n) G) :
    primeRank 2 G = 5 * n := by
  obtain ⟨e⟩ := (isTrialityGroupAt_binary_iff G n hn).mp hG
  let : Finite G := Finite.of_injective e e.injective
  rw [primeRank_equiv 2 e]
  exact twoRank_eq_five_mul n hn

/-- Derived rank transports along the restriction of the actual model equivalence. -/
theorem derived_twoRank_eq_five_mul_of_model (n : ℕ) (hn : 0 < n)
    {G : Type*} [Group G] (hG : IsTrialityGroupAt (2 ^ n) G) :
    primeRank 2 (commutator G) = 5 * n := by
  obtain ⟨e⟩ := (isTrialityGroupAt_binary_iff G n hn).mp hG
  let : Finite G := Finite.of_injective e e.injective
  rw [primeRank_equiv 2 (derivedEquivOfModel n hn e)]
  exact derived_twoRank_eq_five_mul n hn

/-- The automorphism rank table holds for every actual triality-model witness. -/
theorem automorphism_twoRank_eq_five_mul_of_model (n : ℕ) (hn : 0 < n)
    {G : Type*} [Group G] (hG : IsTrialityGroupAt (2 ^ n) G) :
    primeRank 2 (MulAut G) = 5 * n := by
  obtain ⟨e⟩ := (isTrialityGroupAt_binary_iff G n hn).mp hG
  let : Finite G := Finite.of_injective e e.injective
  rw [primeRank_equiv 2 (MulAut.congr e)]
  exact automorphism_twoRank_eq_five_mul n hn

/-- The smaller derived endpoint has the same automorphism rank, for every witness. -/
theorem derived_automorphism_twoRank_eq_five_mul_of_model (n : ℕ) (hn : 0 < n)
    {G : Type*} [Group G] (hG : IsTrialityGroupAt (2 ^ n) G) :
    primeRank 2 (MulAut (commutator G)) = 5 * n := by
  obtain ⟨e⟩ := (isTrialityGroupAt_binary_iff G n hn).mp hG
  let : Finite G := Finite.of_injective e e.injective
  rw [primeRank_equiv 2 (MulAut.congr (derivedEquivOfModel n hn e))]
  exact derived_automorphism_twoRank_eq_five_mul n hn

end Triality.Standard.TwoRank
