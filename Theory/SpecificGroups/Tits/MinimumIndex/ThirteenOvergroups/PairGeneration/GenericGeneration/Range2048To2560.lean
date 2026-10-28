module
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range2048To2560.Block00
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range2048To2560.Block01
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range2048To2560.Block02
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range2048To2560.Block03
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range2048To2560.Block04
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range2048To2560.Block05
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range2048To2560.Block06
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range2048To2560.Block07
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range2048To2560.Block08
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range2048To2560.Block09
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range2048To2560.Block10
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range2048To2560.Block11
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range2048To2560.Block12
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range2048To2560.Block13
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range2048To2560.Block14
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range2048To2560.Block15

/-!
# Whole-group generation for thirteen-pair indices [2048, 2560)

The sixteen kernel-checked recovery blocks cover this interval. Each block
recovers the actual standard involution from `ab` and its left conjugate
by the fixed representative, which supplies both standard generators.
Interval arithmetic selects the applicable block without changing the
published representatives or exception list.

Source: primary ATLAS Tits generators; see `GenericGeneration/source/README.md`.
The recovery words and their emission are documented there.
-/

namespace Tits.MinimumIndexThirteen.PairGeneration.GenericGeneration

/-- Every nonexcluded representative in [2048, 2560) generates the whole carrier. -/
public theorem generation_2048_2560 (k : Fin 3010)
    (hlo : 2048 ≤ k.val) (hhi : k.val < 2560)
    (hk : k ≠ 0) (he : k ∉ exceptionalIndices) :
    pairSubgroup (representative k) = ⊤ := by
  by_cases h0 : k.val < 2080
  · exact generation_2048_2080 k hlo h0 hk he
  by_cases h1 : k.val < 2112
  · exact generation_2080_2112 k (by omega) h1 hk he
  by_cases h2 : k.val < 2144
  · exact generation_2112_2144 k (by omega) h2 hk he
  by_cases h3 : k.val < 2176
  · exact generation_2144_2176 k (by omega) h3 hk he
  by_cases h4 : k.val < 2208
  · exact generation_2176_2208 k (by omega) h4 hk he
  by_cases h5 : k.val < 2240
  · exact generation_2208_2240 k (by omega) h5 hk he
  by_cases h6 : k.val < 2272
  · exact generation_2240_2272 k (by omega) h6 hk he
  by_cases h7 : k.val < 2304
  · exact generation_2272_2304 k (by omega) h7 hk he
  by_cases h8 : k.val < 2336
  · exact generation_2304_2336 k (by omega) h8 hk he
  by_cases h9 : k.val < 2368
  · exact generation_2336_2368 k (by omega) h9 hk he
  by_cases h10 : k.val < 2400
  · exact generation_2368_2400 k (by omega) h10 hk he
  by_cases h11 : k.val < 2432
  · exact generation_2400_2432 k (by omega) h11 hk he
  by_cases h12 : k.val < 2464
  · exact generation_2432_2464 k (by omega) h12 hk he
  by_cases h13 : k.val < 2496
  · exact generation_2464_2496 k (by omega) h13 hk he
  by_cases h14 : k.val < 2528
  · exact generation_2496_2528 k (by omega) h14 hk he
  exact generation_2528_2560 k (by omega) hhi hk he

end Tits.MinimumIndexThirteen.PairGeneration.GenericGeneration
