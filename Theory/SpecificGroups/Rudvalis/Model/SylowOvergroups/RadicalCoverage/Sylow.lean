module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Reduction
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Sylow.Candidate
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Sylow.LocalOrder
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Sylow.TwoPartBound

/-!
# Assembling the Rudvalis max4 Sylow certificate

The checked orbital-rigidity bound excludes 2^15 from the ambient order.
Thus a subgroup of max4 with order 2^14 is an ambient Sylow subgroup: it is
a two-group, and the subgroup index formula forces its index to be odd.
This removes the need for a separate ambient normalizer calculation.

The candidate is defined by explicit words in the preserved max4 generators,
so its containment is already proved. The local order certificate proves that
it has order 2^14, completing `Max4ContainsSylow` without extra premises.

Source: ATLAS `RuG1-max4W1`, GLS3 Table 5.3r, and the Sylow-overgroup use of
[Asc86b] in Aschbacher--Smith, printed p.511 (PDF p.528).
-/

namespace Rudvalis.SylowOvergroups
open RadicalCoverage.SylowCertificate

/-- An actual subgroup of max4 of order 2^14 is ambient Sylow, using the
independently checked ambient two-part bound. -/
public theorem max4ContainsSylow_of_subgroup_card (P : Subgroup Model)
    (hP4 : P ≤ max4) (hcard : Nat.card P = 16384) : Max4ContainsSylow := by
  have hp : IsPGroup 2 P := IsPGroup.of_card (n := 14) hcard
  have hi : ¬ 2 ∣ P.index := by
    intro h
    apply not_two_pow_fifteen_dvd_card_model
    rw [← P.card_mul_index, hcard]
    exact Nat.mul_dvd_mul_left 16384 h
  exact ⟨hp.toSylow hi, hP4⟩

/-- The candidate's local order suffices for max4 Sylow containment. -/
public theorem max4ContainsSylow_of_candidate_card
    (hcard : Nat.card candidate = 16384) : Max4ContainsSylow :=
  max4ContainsSylow_of_subgroup_card candidate candidate_le_max4 hcard

/-- The preserved fourth ATLAS subgroup contains a Sylow two-subgroup of
the ambient degree-4060 Rudvalis model. -/
public theorem max4ContainsSylow : Max4ContainsSylow :=
  max4ContainsSylow_of_candidate_card candidate_card

end Rudvalis.SylowOvergroups
