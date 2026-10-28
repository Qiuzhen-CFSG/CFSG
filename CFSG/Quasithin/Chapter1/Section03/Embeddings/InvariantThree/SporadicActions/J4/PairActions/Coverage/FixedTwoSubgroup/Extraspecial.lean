module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Extraspecial.Reduction

/-!
# Excluding extraspecial J₄ pairs via large two-core normalizers

The order-27 pair product supplies a radical normal subgroup K of the
fixed Sylow subgroup with index at most 32, and a solvable subgroup of
N(K)/K with trivial two-core and order 27 · [S:K]. Exclusion of these subgroups
therefore rules out the entire extraspecial configuration and implies
the requested placement contract.

This assembly remains conditional on the normalizer-quotient calculation.
It does not assert that calculation or the unqualified placement theorem.

Source context: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`), citing Aschbacher's *Overgroups of
Sylow subgroups in sporadic groups* (1986).
-/

public section

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction

/-- Discharging the concrete quotient obstruction completes the extraspecial
placement contract by proving that its input configuration cannot occur. -/
theorem fixedTwoExtraspecialNormalizerPlacement_of_largeNormalizerQuotientExclusion
    (hq : FixedTwoLargeNormalizerQuotientExclusion) :
    FixedTwoExtraspecialNormalizerPlacement := by
  intro _ _ _ S hS R hpair _ hcard _ _ _ _
  have hR : Nat.card R = 27 := by simpa using hcard
  obtain ⟨K, hKT, hTN, _, _, hi, hrad, L, hsol, hcore, hL⟩ :=
    fixedTwo_order27_largeNormalizerQuotient hS hpair hR
  exact (hq S hS K hKT hTN hi hrad L hsol hcore hL).elim

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
