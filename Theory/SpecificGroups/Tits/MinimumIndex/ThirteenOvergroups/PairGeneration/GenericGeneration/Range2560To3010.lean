module
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range2560To3010.Block00
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range2560To3010.Block01
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range2560To3010.Block02
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range2560To3010.Block03
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range2560To3010.Block04
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range2560To3010.Block05
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range2560To3010.Block06
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range2560To3010.Block07
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range2560To3010.Block08
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range2560To3010.Block09
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range2560To3010.Block10
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range2560To3010.Block11
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range2560To3010.Block12
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range2560To3010.Block13
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range2560To3010.Block14

/-!
# Whole-group generation for thirteen-pair indices [2560, 3010)

The fifteen interval certificates recover the actual standard generator `a`
from `ab` and its left conjugate by the fixed representative. Together with
`ab`, this gives both standard generators. Splitting at the certified interval
endpoints covers every nonexceptional index in the stated range.

Source: the primary ATLAS Tits generators; see `GenericGeneration/source/README.md`.
The recovery words in the block modules are checked by the Lean kernel.
-/

namespace Tits.MinimumIndexThirteen.PairGeneration.GenericGeneration

/-- Every nonexcluded representative with index from 2560 through 3009 generates
the whole actual ATLAS carrier. -/
public theorem generation_2560_3010 (k : Fin 3010)
    (hlo : 2560 ≤ k.val) (hhi : k.val < 3010)
    (hk : k ≠ 0) (he : k ∉ exceptionalIndices) :
    pairSubgroup (representative k) = ⊤ := by
  by_cases h0 : k.val < 2592
  · exact generation_2560_2592 k hlo h0 hk he
  by_cases h1 : k.val < 2624
  · exact generation_2592_2624 k (by omega) h1 hk he
  by_cases h2 : k.val < 2656
  · exact generation_2624_2656 k (by omega) h2 hk he
  by_cases h3 : k.val < 2688
  · exact generation_2656_2688 k (by omega) h3 hk he
  by_cases h4 : k.val < 2720
  · exact generation_2688_2720 k (by omega) h4 hk he
  by_cases h5 : k.val < 2752
  · exact generation_2720_2752 k (by omega) h5 hk he
  by_cases h6 : k.val < 2784
  · exact generation_2752_2784 k (by omega) h6 hk he
  by_cases h7 : k.val < 2816
  · exact generation_2784_2816 k (by omega) h7 hk he
  by_cases h8 : k.val < 2848
  · exact generation_2816_2848 k (by omega) h8 hk he
  by_cases h9 : k.val < 2880
  · exact generation_2848_2880 k (by omega) h9 hk he
  by_cases h10 : k.val < 2912
  · exact generation_2880_2912 k (by omega) h10 hk he
  by_cases h11 : k.val < 2944
  · exact generation_2912_2944 k (by omega) h11 hk he
  by_cases h12 : k.val < 2976
  · exact generation_2944_2976 k (by omega) h12 hk he
  by_cases h13 : k.val < 3008
  · exact generation_2976_3008 k (by omega) h13 hk he
  exact generation_3008_3010 k (by omega) hhi hk he

end Tits.MinimumIndexThirteen.PairGeneration.GenericGeneration
