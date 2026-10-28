module

public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range1536To2048.Block00
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range1536To2048.Block01
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range1536To2048.Block02
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range1536To2048.Block03
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range1536To2048.Block04
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range1536To2048.Block05
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range1536To2048.Block06
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range1536To2048.Block07
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range1536To2048.Block08
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range1536To2048.Block09
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range1536To2048.Block10
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range1536To2048.Block11
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range1536To2048.Block12
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range1536To2048.Block13
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range1536To2048.Block14
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range1536To2048.Block15

/-!
# Whole-group generation for thirteen-pair indices [1536, 2048)

Each 32-index block kernel-checks signed words recovering the actual standard
involution from `ab` and its left conjugate by the fixed representative.
The pair then contains both standard generators. Splitting the index interval
assembles these certificates with precisely the original exclusions.

Source: the primary ATLAS Tits generators and the fixed recovery words documented
in `GenericGeneration/source/README.md`. The block certificates are emitted by
`GenericGeneration/source/emit.py` from its unchanged `recovery.json`.
-/

namespace Tits.MinimumIndexThirteen.PairGeneration.GenericGeneration

/-- Every nonexcluded representative in this interval generates the whole carrier. -/
public theorem generation_1536_2048 (k : Fin 3010)
    (hlo : 1536 ≤ k.val) (hhi : k.val < 2048)
    (hk : k ≠ 0) (he : k ∉ exceptionalIndices) :
    pairSubgroup (representative k) = ⊤ := by
  by_cases h1792 : k.val < 1792
  · by_cases h1664 : k.val < 1664
    · by_cases h1600 : k.val < 1600
      · by_cases h1568 : k.val < 1568
        · exact generation_1536_1568 k (by omega) (by omega) hk he
        · exact generation_1568_1600 k (by omega) (by omega) hk he
      · by_cases h1632 : k.val < 1632
        · exact generation_1600_1632 k (by omega) (by omega) hk he
        · exact generation_1632_1664 k (by omega) (by omega) hk he
    · by_cases h1728 : k.val < 1728
      · by_cases h1696 : k.val < 1696
        · exact generation_1664_1696 k (by omega) (by omega) hk he
        · exact generation_1696_1728 k (by omega) (by omega) hk he
      · by_cases h1760 : k.val < 1760
        · exact generation_1728_1760 k (by omega) (by omega) hk he
        · exact generation_1760_1792 k (by omega) (by omega) hk he
  · by_cases h1920 : k.val < 1920
    · by_cases h1856 : k.val < 1856
      · by_cases h1824 : k.val < 1824
        · exact generation_1792_1824 k (by omega) (by omega) hk he
        · exact generation_1824_1856 k (by omega) (by omega) hk he
      · by_cases h1888 : k.val < 1888
        · exact generation_1856_1888 k (by omega) (by omega) hk he
        · exact generation_1888_1920 k (by omega) (by omega) hk he
    · by_cases h1984 : k.val < 1984
      · by_cases h1952 : k.val < 1952
        · exact generation_1920_1952 k (by omega) (by omega) hk he
        · exact generation_1952_1984 k (by omega) (by omega) hk he
      · by_cases h2016 : k.val < 2016
        · exact generation_1984_2016 k (by omega) (by omega) hk he
        · exact generation_2016_2048 k (by omega) (by omega) hk he

end Tits.MinimumIndexThirteen.PairGeneration.GenericGeneration
