module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.CommutingComponents.PairIndex.Geometry
public import Theory.GroupTheory.CComponent.PairNormalizerIndex

/-!
# Reduction of the identified Suzuki-pair index

The finite-group argument combines a factor-normalizer bound with an ambient
factor interchange in a proper normalizer. It derives normality of the actual
join and uses maximality to put the interchange in M, giving exactly two cosets.

This module retains assembly of `IdentifiedPairIndex`. The theorem below is
conditional on the two geometric obligations; it does not establish the
unconditional `identifiedPairIndex` until they have been proved.

Source: Malle, J. Algebra 139 (1991), 52--69,
DOI 10.1016/0021-8693(91)90283-E; the Sz(q)≀2 entry in the unconditional
list in the proof of Theorem 5 of arXiv:0910.4758, pp.2--3.
-/

public section

namespace ReeF4.MaximalSubgroups.CommutingComponents

/-- Assemble the index from two independent geometric calculations. The
carrier equivalences are precisely the local inputs of `IdentifiedPairIndex`. -/
theorem identifiedPairIndex_of_factorNormalizer_of_pairSwap
    (hN : IdentifiedFactorNormalizer) (hswap : IdentifiedPairSwap) :
    IdentifiedPairIndex := by
  intro m hm M hM hsolv hR L K hL hK hne hc eL eK
  obtain ⟨hp, s, hsL, hsK⟩ := hswap m hm M hM hsolv hR L K hL hK hne hc eL eK
  exact Subgroup.index_sup_eq_two_of_isCComponent_of_normalizer_le_of_ambient_swap
    hM hR hL hK hne hc (hN m hm M hM hsolv hR L K hL hK hne hc eL eK)
    hp s hsL hsK

end ReeF4.MaximalSubgroups.CommutingComponents
