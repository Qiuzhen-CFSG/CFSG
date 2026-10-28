module

public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.Normalization.Assembly
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.Normalization.Lower.Relations
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.Normalization.Lower.ShortPair
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.Normalization.Lower.MixedPair

/-!
# Lower normalization in the smallest triality cover

Normalize the three short sections using the genuine arms Levi torus, keeping
all long sections. The commuting and upper relations persist. The proved
short–short exchange removes its central defect by scalar invariance; it then
supplies additivity for the mixed exchange, whose central defect vanishes by
scalar-equivariant uniqueness. Both lower exchanges have corrections strictly
above the exchanged roots. Thus `exists_lowerNormalized` needs only the
original commuting and upper relations.

Source: GLS3 §2.4.5(b)(4)–(5), §6.1;
Aschbacher–Smith I.1.3 (PDF p.418).
-/

public section
open Triality.Standard PerfectCentralCovering
namespace Triality.Standard.CentralCovers.TwoPrimary.SmallField
open LowerNormalization
noncomputable section
local notation "G" => BinaryCarrier 1 Nat.zero_lt_one
local notation "π" => universalProjection G

/-- Reduce lower normalization to two precise calculations on torus-equivariant
sections. The theorem below supplies both calculations. -/
theorem exists_lowerNormalized_of_torus_calculations
    (hshort : ∀ M : RootSections 1 Nat.zero_lt_one π,
      ArmsTorusNormalized M → CommutingPairs M → UpperRelations M → ShortPairRelation M)
    (hmixed : ∀ M : RootSections 1 Nat.zero_lt_one π,
      ArmsTorusNormalized M → CommutingPairs M → UpperRelations M →
        ShortPairRelation M → MixedPairRelation M)
    (L : RootSections 1 Nat.zero_lt_one π) (hcomm : CommutingPairs L)
    (hu : UpperRelations L) :
    ∃ M : RootSections 1 Nat.zero_lt_one π,
      L.longRoot = M.longRoot ∧ LowerRelations M := by
  obtain ⟨M, hl, ht, hc, hu⟩ := exists_armsTorusNormalized_of_upper
    (universalProjection_surjective G) (universalProjection_ker_le_center G) L hcomm hu
  have hs := hshort M ht hc hu
  exact ⟨M, hl, (hmixed M ht hc hu hs).pairExchange, hs.pairExchange⟩

/-- Normalize both lower exchanges while retaining all three long sections.
The short–short relation is proved first in the common torus-equivariant family
and supplies the polynomial input to the mixed relation. -/
theorem exists_lowerNormalized
    (L : RootSections 1 Nat.zero_lt_one π) (hcomm : CommutingPairs L)
    (hu : UpperRelations L) :
    ∃ M : RootSections 1 Nat.zero_lt_one π,
      L.longRoot = M.longRoot ∧ LowerRelations M :=
  exists_lowerNormalized_of_torus_calculations
    shortPairRelation_of_armsTorusNormalized mixedPairRelation_of_armsTorusNormalized
    L hcomm hu

end
end Triality.Standard.CentralCovers.TwoPrimary.SmallField
