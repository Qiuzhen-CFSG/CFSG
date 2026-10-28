module
public import Theory.Mathieu.M12.SmallParabolicPair.SylowGeometry.WordCompleteness
/-! Kernel-checked cardinalities from the short-word normalizer certificate. -/
@[expose] public section
namespace Sporadic.Mathieu.M12SmallPair.SylowEnumeration
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

theorem wordCarrier_card : wordCarrier.card = 192 := by decide +kernel

theorem wordIntersection_card :
    (wordCarrier.filter CentralizesCenterPerm).card = 64 := by decide +kernel

theorem secondParabolic_card : Nat.card secondParabolic = 192 := by
  rw [secondParabolic_card_eq_finset wordCarrier mem_wordCarrier_iff, wordCarrier_card]

theorem intersection_card : Nat.card sylowCandidate = 64 := by
  rw [sylowCandidate_card_eq_finset (wordCarrier.filter CentralizesCenterPerm)
    (fun p => by simp only [Finset.mem_filter, mem_wordCarrier_iff, and_assoc]),
    wordIntersection_card]
end Sporadic.Mathieu.M12SmallPair.SylowEnumeration
