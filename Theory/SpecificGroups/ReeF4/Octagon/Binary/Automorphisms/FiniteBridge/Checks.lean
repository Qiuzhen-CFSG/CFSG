module
public import Theory.SpecificGroups.ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.Checks11

/-! All 2925 literal line triples have the certified predecessor and unique set key. -/
public section
namespace ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.LineData
theorem valid (i : Fin 2925) : Valid i :=
  (interval_join (interval_join (interval_join valid0000 (interval_join valid0256 valid0512)) (interval_join valid0768 (interval_join valid1024 valid1280))) (interval_join (interval_join valid1536 (interval_join valid1792 valid2048)) (interval_join valid2304 (interval_join valid2560 valid2816)))) i (Nat.zero_le _) i.isLt
end ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.LineData
