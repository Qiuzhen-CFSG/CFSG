module

public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range0512To1024.Block00
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range0512To1024.Block01
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range0512To1024.Block02
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range0512To1024.Block03
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range0512To1024.Block04
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range0512To1024.Block05
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range0512To1024.Block06
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range0512To1024.Block07
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range0512To1024.Block08
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range0512To1024.Block09
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range0512To1024.Block10
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range0512To1024.Block11
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range0512To1024.Block12
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range0512To1024.Block13
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range0512To1024.Block14
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range0512To1024.Block15

/-!
# Whole-group generation for thirteen-pair indices [512, 1024)

The sixteen checked recovery blocks cover this interval. Each certificate
recovers the actual standard generator `a` from `ab` and its left conjugate,
so the pair contains both standard generators of the ATLAS carrier.

Source: the primary ATLAS Tits generators; see `GenericGeneration/source/README.md`.
The representative codes and the exact exceptional-index list are unchanged.
-/

namespace Tits.MinimumIndexThirteen.PairGeneration.GenericGeneration

/-- Every nonexcluded representative with index in [512, 1024) generates the whole carrier. -/
public theorem generation_512_1024 (k : Fin 3010)
    (hlo : 512 ≤ k.val) (hhi : k.val < 1024)
    (hk : k ≠ 0) (he : k ∉ exceptionalIndices) :
    pairSubgroup (representative k) = ⊤ := by
  by_cases h544 : k.val < 544
  · exact generation_512_544 k hlo h544 hk he
  by_cases h576 : k.val < 576
  · exact generation_544_576 k (by omega) h576 hk he
  by_cases h608 : k.val < 608
  · exact generation_576_608 k (by omega) h608 hk he
  by_cases h640 : k.val < 640
  · exact generation_608_640 k (by omega) h640 hk he
  by_cases h672 : k.val < 672
  · exact generation_640_672 k (by omega) h672 hk he
  by_cases h704 : k.val < 704
  · exact generation_672_704 k (by omega) h704 hk he
  by_cases h736 : k.val < 736
  · exact generation_704_736 k (by omega) h736 hk he
  by_cases h768 : k.val < 768
  · exact generation_736_768 k (by omega) h768 hk he
  by_cases h800 : k.val < 800
  · exact generation_768_800 k (by omega) h800 hk he
  by_cases h832 : k.val < 832
  · exact generation_800_832 k (by omega) h832 hk he
  by_cases h864 : k.val < 864
  · exact generation_832_864 k (by omega) h864 hk he
  by_cases h896 : k.val < 896
  · exact generation_864_896 k (by omega) h896 hk he
  by_cases h928 : k.val < 928
  · exact generation_896_928 k (by omega) h928 hk he
  by_cases h960 : k.val < 960
  · exact generation_928_960 k (by omega) h960 hk he
  by_cases h992 : k.val < 992
  · exact generation_960_992 k (by omega) h992 hk he
  exact generation_992_1024 k (by omega) hhi hk he

end Tits.MinimumIndexThirteen.PairGeneration.GenericGeneration
