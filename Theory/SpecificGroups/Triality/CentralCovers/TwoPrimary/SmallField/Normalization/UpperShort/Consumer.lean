module

public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.Normalization.UpperShort
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.Normalization

/-!
# Applying the upper trace calculations to normalization

The upper trace and comparison calculations supply the literal two arguments
of `exists_normalizingAdjustment_of_remaining_relations`. The lower
normalization remains independent. All three inputs are explicit until their
respective calculations have been proved; the conclusion is the original
central-adjustment witness, with the original projection and root sections.

Source: GLS3 §2.4.5 and §6.1; Aschbacher–Smith I.1.3 (PDF p.418).
-/

public section
open Triality.Standard PerfectCentralCovering
namespace Triality.Standard.CentralCovers.TwoPrimary.SmallField
noncomputable section
local notation "G" => BinaryCarrier 1 Nat.zero_lt_one
local notation "π" => universalProjection G
local notation "hf" => universalProjection_surjective G
local notation "hk" => universalProjection_ker_le_center G

/-- Actual application to the central-adjustment consumer. The highest trace,
commutator comparison, and lower normalization still require their producers. -/
theorem exists_normalizingAdjustment_of_highestTrace_and_comparison
    (hcomm : CommutingPairs universalRootSections)
    (htrace : UpperShort.HighestShortTrace π hf hk)
    (hcompare : longPairHighest universalRootSections = highestLift π hf hk)
    (hlower : ∀ L : RootSections 1 Nat.zero_lt_one π,
      CommutingPairs L → UpperRelations L →
      ∃ M : RootSections 1 Nat.zero_lt_one π,
        L.longRoot = M.longRoot ∧ LowerRelations M) :
    ∃ A : CentralAdjustment π,
      (A.adjusted hk universalRootSections).HigherCommutators := by
  obtain ⟨h03, h23⟩ := upperShort_relations_of_trace_and_comparison hcomm htrace hcompare
  exact exists_normalizingAdjustment_of_remaining_relations hcomm h03 h23 hlower

/-- The completed upper-short calculation feeds the remaining normalization
consumer; the lower-normalization producer remains the sole explicit
conditional input. -/
theorem exists_normalizingAdjustment_of_upperShort_relations
    (hcomm : CommutingPairs universalRootSections)
    (hlower : ∀ L : RootSections 1 Nat.zero_lt_one π,
      CommutingPairs L → UpperRelations L →
      ∃ M : RootSections 1 Nat.zero_lt_one π,
        L.longRoot = M.longRoot ∧ LowerRelations M) :
    ∃ A : CentralAdjustment π,
      (A.adjusted hk universalRootSections).HigherCommutators := by
  obtain ⟨h03, h23⟩ := upperShort_relations hcomm
  exact exists_normalizingAdjustment_of_remaining_relations hcomm h03 h23 hlower

end
end Triality.Standard.CentralCovers.TwoPrimary.SmallField
