module

public import Theory.SpecificGroups.BinaryLinear.OrderedResidualConjugators.ResidualUpper

/-!
# Successive conjugators for binary parabolic residuals

The adjacent basis swap belongs to the next literal minimal parabolic.
Residual recognition identifies each embedded O² with its cubic and
incident-root subgroup, so the root-join calculation gives the required
successive residual join with right conjugation. No residual bound or
generation hypothesis remains. The result holds in every dimension,
including the source dimensions three, four and five.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
the conjugator step in the proof of Lemma 12.8.10(5), printed p.854
(PDF p.871), `refs/quasithin.pdf`.
-/

public section

namespace BinaryLinear.OrderedResidualConjugators
open OuterCyclic InvariantNodeActions

/-- The next minimal parabolic contains a right conjugator generating the
next initial residual join from the previous one. -/
theorem exists_initialResiduals_conjugator {m : ℕ} (b : Basis m) (r : ℕ)
    (hpos : 1 ≤ r) (hr : r < m) :
    ∃ s ∈ minimalParabolic b ⟨r, hr⟩,
      initialResiduals b (r + 1) = initialResiduals b r ⊔
        (initialResiduals b r).map (MulAut.conj s⁻¹).toMonoidHom :=
  ⟨adjacentSwap b ⟨r, hr⟩, adjacentSwap_mem_minimalParabolic b ⟨r, hr⟩,
    initialResiduals_successor b r hpos hr⟩

end BinaryLinear.OrderedResidualConjugators
