module

public import Theory.SpecificGroups.Triality.StandardTwoRank.Automorphisms
public import Theory.SpecificGroups.Triality.StandardTwoRank.Derived
public import Theory.GroupTheory.AutomorphismOvergroupCore

/-!
# Unconditional ranks of binary triality and its automorphism group

The genuine simple and perfect carrier instances discharge the hypotheses of
the sharp automorphism estimate. Conjugation embeds the centerless carrier
into its automorphism group, so its exact rank 5n gives equality there too.
The inclusion equivalence from the commutator to the carrier transports both
calculations to the derived group. Every result includes n = 1.

Source: Aschbacher–Smith, the rank table on printed p.356 and the field pair
in 16.1.7(3a), pp.1171–1172 (`refs/quasithin.pdf`). The graph-field action and
central quotient are those of `Triality.Standard`, throughout.
-/

public section
noncomputable section

namespace Triality.Standard.TwoRank
open Theory.GroupTheory

/-- The sharp automorphism bound, with simplicity and perfectness discharged. -/
theorem automorphism_twoRank_le_five_mul (n : ℕ) (hn : 0 < n) :
    primeRank 2 (MulAut (BinaryCarrier n hn)) ≤ 5 * n :=
  Automorphisms.automorphism_twoRank_le_five_mul n hn

/-- The automorphism rank equals the intrinsic rank, including exponent one. -/
theorem automorphism_twoRank_eq_five_mul (n : ℕ) (hn : 0 < n) :
    primeRank 2 (MulAut (BinaryCarrier n hn)) = 5 * n := by
  apply Nat.le_antisymm (automorphism_twoRank_le_five_mul n hn)
  rw [← twoRank_eq_five_mul n hn]
  exact primeRank_le_of_injective 2 (MulAut.conj : BinaryCarrier n hn →* _)
    (conj_injective_of_center_eq_bot (binaryCarrier_center_eq_bot n hn))

/-- Perfectness gives the exact rank of the actual derived subgroup. -/
theorem derived_twoRank_eq_five_mul (n : ℕ) (hn : 0 < n) :
    primeRank 2 (commutator (BinaryCarrier n hn)) = 5 * n := by
  rw [primeRank_equiv 2 (Perfectness.binaryCommutatorEquiv n hn)]
  exact twoRank_eq_five_mul n hn

/-- Automorphisms transport along the genuine commutator inclusion equivalence. -/
theorem derived_automorphism_twoRank_eq_five_mul (n : ℕ) (hn : 0 < n) :
    primeRank 2 (MulAut (commutator (BinaryCarrier n hn))) = 5 * n := by
  rw [primeRank_equiv 2 (MulAut.congr (Perfectness.binaryCommutatorEquiv n hn))]
  exact automorphism_twoRank_eq_five_mul n hn

/-- The unconditional derived-automorphism estimate used by the field pair. -/
theorem derived_automorphism_twoRank_le_five_mul (n : ℕ) (hn : 0 < n) :
    primeRank 2 (MulAut (commutator (BinaryCarrier n hn))) ≤ 5 * n :=
  (derived_automorphism_twoRank_eq_five_mul n hn).le

end Triality.Standard.TwoRank
