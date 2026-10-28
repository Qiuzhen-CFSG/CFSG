module
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Recovery

/-!
# Whole-group generation for thirteen-pair indices [3008, 3010)

The signed recovery words reconstruct the actual standard involution. The
pair already contains `ab`, so the checked identities give both generators.
Only zero and the exact published exception list are excluded.

Source: primary ATLAS Tits generators; see `GenericGeneration/source/README.md`.
Untrusted word discovery: `source/discover.py`; certificate emission: `source/emit.py`.
-/

namespace Tits.MinimumIndexThirteen.PairGeneration.GenericGeneration

private def words (i : Fin 2) : List (Bool × Int) :=
  if i.val < 1 then
    [(false, -2), (true, 2), (false, -5), (true, -2), (false, 3), (true, 1), (false, 1)]
  else
    [(false, 2), (true, -5), (false, -5), (true, 1), (false, -1), (true, -6), (false, 2)]

set_option maxRecDepth 20000 in
private theorem checked : blockTest 3008 2 words = true := by
  decide +kernel

/-- Every nonexcluded representative in this interval generates the whole carrier. -/
public theorem generation_3008_3010 (k : Fin 3010)
    (hlo : 3008 ≤ k.val) (hhi : k.val < 3010)
    (hk : k ≠ 0) (he : k ∉ exceptionalIndices) :
    pairSubgroup (representative k) = ⊤ :=
  blockTest_sound 3008 2 words checked k hlo hhi hk he

end Tits.MinimumIndexThirteen.PairGeneration.GenericGeneration
