module

public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range0032To0512.Block00
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range0032To0512.Block01
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range0032To0512.Block02
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range0032To0512.Block03
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range0032To0512.Block04
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range0032To0512.Block05
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range0032To0512.Block06
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range0032To0512.Block07
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range0032To0512.Block08
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range0032To0512.Block09
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range0032To0512.Block10
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range0032To0512.Block11
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range0032To0512.Block12
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range0032To0512.Block13
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range0032To0512.Block14

/-!
# Whole-group generation for thirteen-pair indices [32, 512)

For each nonexceptional representative in this interval, a kernel-checked
signed word in `ab` and its left conjugate recovers the actual standard
involution `a`. The pair then contains `b = a⁻¹(ab)`, so it generates the
whole ATLAS carrier. The fifteen bounded certificates use precisely the
published `representativeCode` and `exceptionalIndices` definitions.

This module combines those certificates by interval arithmetic and supplies
the [32, 512) branch for the universal generic-pair generation assembly.

Source: the primary ATLAS Tits generators; see `GenericGeneration/source/README.md`
for attribution, word conventions, and the untrusted recovery-word data.
-/

namespace Tits.MinimumIndexThirteen.PairGeneration.GenericGeneration

/-- Every nonzero, nonexceptional representative at indices 32 through 511
has its literal thirteen-pair subgroup equal to the whole carrier. -/
public theorem generation_32_512 (k : Fin 3010)
    (hlo : 32 ≤ k.val) (hhi : k.val < 512)
    (hk : k ≠ 0) (he : k ∉ exceptionalIndices) :
    pairSubgroup (representative k) = ⊤ := by
  by_cases h64 : k.val < 64
  · exact generation_32_64 k hlo h64 hk he
  by_cases h96 : k.val < 96
  · exact generation_64_96 k (by omega) h96 hk he
  by_cases h128 : k.val < 128
  · exact generation_96_128 k (by omega) h128 hk he
  by_cases h160 : k.val < 160
  · exact generation_128_160 k (by omega) h160 hk he
  by_cases h192 : k.val < 192
  · exact generation_160_192 k (by omega) h192 hk he
  by_cases h224 : k.val < 224
  · exact generation_192_224 k (by omega) h224 hk he
  by_cases h256 : k.val < 256
  · exact generation_224_256 k (by omega) h256 hk he
  by_cases h288 : k.val < 288
  · exact generation_256_288 k (by omega) h288 hk he
  by_cases h320 : k.val < 320
  · exact generation_288_320 k (by omega) h320 hk he
  by_cases h352 : k.val < 352
  · exact generation_320_352 k (by omega) h352 hk he
  by_cases h384 : k.val < 384
  · exact generation_352_384 k (by omega) h384 hk he
  by_cases h416 : k.val < 416
  · exact generation_384_416 k (by omega) h416 hk he
  by_cases h448 : k.val < 448
  · exact generation_416_448 k (by omega) h448 hk he
  by_cases h480 : k.val < 480
  · exact generation_448_480 k (by omega) h480 hk he
  exact generation_480_512 k (by omega) hhi hk he

end Tits.MinimumIndexThirteen.PairGeneration.GenericGeneration
