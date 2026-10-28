module

public import Theory.SpecificGroups.Held.AutomorphismLocalPair.SeedIdentification
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.QuasithinBasic

/-!
# The marked elementary subgroup gives Held two-rank at least six

Row 20 of the checked intrinsic local enumeration is an elementary group of
order 64. Include it through the actual representative subgroup into Held.
Source: GLS3 Table 5.3p; Aschbacher–Smith A.2.12, printed p.36.
-/

namespace Held
open LocalPairs.SylowGeometry.Calculations
open TwoLocalCandidates.MaximalNormalizerCatalogue
open TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration
/-- The actual order-64 local row supplies the Held rank obstruction. -/
public theorem six_le_twoRank : 6 ≤ primeRank 2 He := by
  have h := (AutomorphismLocalPair.representative_normal_elementary_order64_iff (entry 20)).mpr
    (Or.inl rfl)
  let : IsElementaryAbelian 2 (entry 20) := h.2.1
  have hb : 6 ≤ primeRank 2 representative := IsElementaryAbelian.primeRank_ge_of_card
    (entry 20) h.2.2
  exact hb.trans (Theory.GroupTheory.primeRank_le_of_injective 2
    representative.subtype Subtype.val_injective)
end Held
