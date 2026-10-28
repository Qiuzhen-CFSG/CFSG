module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Sylow.LocalOrder.TwoGroup
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Sylow.LocalOrder.Separation
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Sylow.TwoPartBound

/-!
# Order of the explicit Rudvalis max4 candidate

Kernel-checked word and collection identities prove that the candidate is
a two-group. Its 16384 binary products are distinct, as witnessed by their
images of the point pair (0,1). Lagrange's theorem and the independently
proved exclusion of 2^15 from the ambient order give the matching upper bound.
Thus the original word-generated subgroup has order exactly 16384, with
no extra premises and no dependence on unfinished model-order certificates.

Source: the preserved ATLAS `RuG1-max4W1` and degree-4060 permutations;
GLS3 Table 5.3r, printed p.279. This calculation supplies the Sylow containment
used in Aschbacher--Smith, printed p.511 (PDF p.528), citing [Asc86b].
-/

namespace Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate

/-- The explicit candidate in the preserved max4 subgroup has order 2^14. -/
public theorem candidate_card : Nat.card candidate = 16384 := by
  obtain ⟨n, hn⟩ := LocalOrder.candidate_isTwoGroup.exists_card_eq
  have hnle : n ≤ 14 := by
    by_contra! h
    apply not_two_pow_fifteen_dvd_card_model
    have hd : Nat.card candidate ∣ Nat.card Model :=
      ⟨candidate.index, candidate.card_mul_index.symm⟩
    rw [hn] at hd
    exact (Nat.pow_dvd_pow 2 h).trans hd
  apply le_antisymm
  · rw [hn]
    exact Nat.pow_le_pow_right (by decide) hnle
  · exact LocalOrder.candidate_card_lower

end Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate
