module
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Recovery
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range1024To1536.Block00
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range1024To1536.Block01
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range1024To1536.Block02
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range1024To1536.Block03
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range1024To1536.Block04
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range1024To1536.Block05
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range1024To1536.Block06
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range1024To1536.Block07
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range1024To1536.Block08
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range1024To1536.Block09
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range1024To1536.Block10
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range1024To1536.Block11
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range1024To1536.Block12
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range1024To1536.Block13
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range1024To1536.Block14
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range1024To1536.Block15

/-!
# Whole-group generation for thirteen-pair indices [1024, 1536)

Sixteen kernel-checked recovery blocks reconstruct the actual standard
involution from `ab` and its left conjugate by each fixed representative.
Since the pair also contains `ab`, it contains both standard generators.
Interval arithmetic combines the blocks without any additional premise.
The fixed exception indices 1441 and 1449 retain their separate obligations.

Source: the primary ATLAS Tits generators and the unchanged representative
codes; see `GenericGeneration/source/README.md`. The block certificates use
its signed recovery witnesses and `source/emit.py`.
-/

namespace Tits.MinimumIndexThirteen.PairGeneration.GenericGeneration

/-- Every nonexcluded representative in [1024, 1536) generates the whole carrier. -/
public theorem generation_1024_1536 (k : Fin 3010)
    (hlo : 1024 ≤ k.val) (hhi : k.val < 1536)
    (hk : k ≠ 0) (he : k ∉ exceptionalIndices) :
    pairSubgroup (representative k) = ⊤ := by
  by_cases h1280 : k.val < 1280
  · by_cases h1152 : k.val < 1152
    · by_cases h1088 : k.val < 1088
      · by_cases h1056 : k.val < 1056
        · exact generation_1024_1056 k (by omega) (by omega) hk he
        · exact generation_1056_1088 k (by omega) (by omega) hk he
      · by_cases h1120 : k.val < 1120
        · exact generation_1088_1120 k (by omega) (by omega) hk he
        · exact generation_1120_1152 k (by omega) (by omega) hk he
    · by_cases h1216 : k.val < 1216
      · by_cases h1184 : k.val < 1184
        · exact generation_1152_1184 k (by omega) (by omega) hk he
        · exact generation_1184_1216 k (by omega) (by omega) hk he
      · by_cases h1248 : k.val < 1248
        · exact generation_1216_1248 k (by omega) (by omega) hk he
        · exact generation_1248_1280 k (by omega) (by omega) hk he
  · by_cases h1408 : k.val < 1408
    · by_cases h1344 : k.val < 1344
      · by_cases h1312 : k.val < 1312
        · exact generation_1280_1312 k (by omega) (by omega) hk he
        · exact generation_1312_1344 k (by omega) (by omega) hk he
      · by_cases h1376 : k.val < 1376
        · exact generation_1344_1376 k (by omega) (by omega) hk he
        · exact generation_1376_1408 k (by omega) (by omega) hk he
    · by_cases h1472 : k.val < 1472
      · by_cases h1440 : k.val < 1440
        · exact generation_1408_1440 k (by omega) (by omega) hk he
        · exact generation_1440_1472 k (by omega) (by omega) hk he
      · by_cases h1504 : k.val < 1504
        · exact generation_1472_1504 k (by omega) (by omega) hk he
        · exact generation_1504_1536 k (by omega) (by omega) hk he

end Tits.MinimumIndexThirteen.PairGeneration.GenericGeneration
