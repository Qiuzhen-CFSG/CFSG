module

public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.HighestLift
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.Pairs
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.Normalization.LongPair
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.Normalization.Lower
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.Normalization.UpperShort

/-!
# Normalizing the five interacting pairs in the smallest triality cover

Under `CommutingPairs`, normalize the long–long exchange and apply the proved
upper short-pair trace relations. Arms-torus normalization then supplies the
two lower exchanges while retaining all long sections. Centrality transports
the upper relations and commuting pairs to the final root system; its additive
difference from the original sections is the required `CentralAdjustment`.
The assembly covers every parameter and both exchange directions.

`exists_normalizingAdjustment` retains only the independent ten-pair
commutation hypothesis. `Normalization.Consumer` applies it to the literal
canonical kernel without introducing an import cycle. Discharging that
commutation hypothesis remains with the full small-field assembly.
Sources: GLS3 §2.4.5 and §6.1; Aschbacher–Smith A.2.4 and I.1.3
(PDF pp.44 and 418).
-/

public section

open Triality.Standard PerfectCentralCovering
namespace Triality.Standard.CentralCovers.TwoPrimary.SmallField
noncomputable section

local notation "G" => BinaryCarrier 1 Nat.zero_lt_one
local notation "π" => universalProjection G
local notation "hk" => universalProjection_ker_le_center G

/-- The two upper short-pair calculations and the independent lower normalization
suffice for the original central-adjustment witness. -/
theorem exists_normalizingAdjustment_of_remaining_relations
    (hcomm : CommutingPairs universalRootSections)
    (h03 : PairExchange (longPairSections hk universalRootSections hcomm) 0 3)
    (h23 : PairExchange (longPairSections hk universalRootSections hcomm) 2 3)
    (hlower : ∀ L : RootSections 1 Nat.zero_lt_one π,
      CommutingPairs L → UpperRelations L →
      ∃ M : RootSections 1 Nat.zero_lt_one π,
        L.longRoot = M.longRoot ∧ LowerRelations M) :
    ∃ A : CentralAdjustment π,
      (A.adjusted hk universalRootSections).HigherCommutators := by
  let L := longPairSections hk universalRootSections hcomm
  have hu : UpperRelations L :=
    ⟨h03, longPairSections_pairExchange hk universalRootSections hcomm, h23⟩
  have hc : CommutingPairs L := longPairSections_commutingPairs hk universalRootSections hcomm
  obtain ⟨M, hlong, hl⟩ := hlower L hc hu
  have huM : UpperRelations M := hu.of_same_long hk hlong
  have hcM : CommutingPairs M := (commutingPairs_iff hk L M).mp hc
  refine ⟨adjustmentBetween hk universalRootSections M, ?_⟩
  rw [adjustmentBetween_adjusted]
  exact higherCommutators_of_pairs M hcM huM hl

/-- The five interacting root pairs can be normalized by additive corrections
in the literal central kernel. Only the independent commuting-pair hypothesis
remains; the upper trace relations and lower normalization are discharged. -/
theorem exists_normalizingAdjustment
    (hcomm : CommutingPairs universalRootSections) :
    ∃ A : CentralAdjustment π,
      (A.adjusted hk universalRootSections).HigherCommutators := by
  obtain ⟨h03, h23⟩ := upperShort_relations hcomm
  exact exists_normalizingAdjustment_of_remaining_relations hcomm h03 h23
    exists_lowerNormalized

end
end Triality.Standard.CentralCovers.TwoPrimary.SmallField
