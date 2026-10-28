module

public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Pilot
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range0032To0512
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range0512To1024
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range1024To1536
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range1536To2048
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range2048To2560
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Range2560To3010

/-!
# Checked whole-group generation for all generic thirteen-pairs

`pairSubgroup_representative_eq_top` proves generation for every nonzero,
nonexceptional member of the exact 3010-entry representative family. The
bounded certificates recover the actual standard involution by signed words
in `ab` and its left conjugate, then obtain the other standard generator from
`ab`. Splitting at the certified interval boundaries covers all 2982 cases.

This discharges precisely the `hgeneric` premise of the parent
`generation_of_three_certificates` reduction. Normalizer double-coset coverage
and exceptional derived-subgroup containment are separate inputs of that
reduction; neither is needed for this whole-group generation theorem.

Source: the primary ATLAS Tits entry and the fixed representative family in
`source/representative-codes.json`. See `GenericGeneration/source/README.md`
for the discovery algorithm, conventions, and bounded compilation measurements.
-/

namespace Tits.MinimumIndexThirteen.PairGeneration
open GenericGeneration

/-- The marked cyclic thirteen-subgroup and its left conjugate by any nonzero,
nonexceptional representative generate the whole ATLAS carrier. -/
public theorem pairSubgroup_representative_eq_top (k : Fin 3010)
    (hk : k ≠ 0) (he : k ∉ exceptionalIndices) :
    pairSubgroup (representative k) = ⊤ := by
  by_cases h32 : k.val < 32
  · exact generation_0_32 k (Nat.zero_le _) h32 hk he
  by_cases h512 : k.val < 512
  · exact generation_32_512 k (by omega) h512 hk he
  by_cases h1024 : k.val < 1024
  · exact generation_512_1024 k (by omega) h1024 hk he
  by_cases h1536 : k.val < 1536
  · exact generation_1024_1536 k (by omega) h1536 hk he
  by_cases h2048 : k.val < 2048
  · exact generation_1536_2048 k (by omega) h2048 hk he
  by_cases h2560 : k.val < 2560
  · exact generation_2048_2560 k (by omega) h2560 hk he
  exact generation_2560_3010 k (by omega) k.isLt hk he

end Tits.MinimumIndexThirteen.PairGeneration
