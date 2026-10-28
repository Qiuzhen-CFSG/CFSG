module

public import Theory.SpecificGroups.Held.Model.FourPointBase

/-!
# A power-doubling conjugator for the Held seventeen-cycle

An explicit word in the retained ATLAS generators satisfies `c * n = n * c²`,
where `c = ab`. The certified four-point base detects this equality in the
actual Held carrier, so conjugation by `n⁻¹` sends `c` to `c²`. No Sylow or
group-order premise is used. Repeated conjugation reduces the sixteen nonzero
exponents to representatives 1 and 3.

The untrusted GAP search is retained in `Source/FindPowerConjugator.g`.
The four point checks use kernel reduction against the literal permutation
tables from `Model/Source/HeG1-p2058B0.g1` and `.g2`. Their right-action
convention has already been converted by `Model/PermutationData.lean`.
The four-point base itself is established by the existing graph certificates.
-/

namespace Held.Realization.MarkedConjugacy.NormalizedPairs

private def normalizerWord : He :=
  a * (b ^ 2)⁻¹ * a * (b ^ 2) * a * (b ^ 2)⁻¹ * a * (b ^ 2) * a * (b ^ 2)⁻¹ * a * (b ^ 3) * a * b * a * (b ^ 2) * a * b * a * b⁻¹ * a * (b ^ 2)⁻¹ * a * b⁻¹ * a * b⁻¹ * a * (b ^ 2)⁻¹ * a * (b ^ 2) * a * b * a * (b ^ 2) * a * b⁻¹ * a * b * a * (b ^ 3)⁻¹ * a * (b ^ 2) * a * (b ^ 2) * a * (b ^ 2)⁻¹ * a * (b ^ 2) * a * b⁻¹

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
/-- An actual inner conjugation squares `ab`; this is not a Sylow assertion. -/
public theorem exists_powerDoubler :
    ∃ d : He, MulAut.conj d (a * b) = (a * b) ^ 2 := by
  have h : (a * b) * normalizerWord = normalizerWord * (a * b) ^ 2 := by
    apply eq_of_four_point_images
    decide +kernel
  refine ⟨normalizerWord⁻¹, ?_⟩
  simp only [MulAut.conj_apply, inv_inv, mul_assoc, h, inv_mul_cancel_left]

end Held.Realization.MarkedConjugacy.NormalizedPairs
