module
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.GenericGeneration.Recovery

/-!
# Whole-group generation for thirteen-pair indices [2016, 2048)

The signed recovery words reconstruct the actual standard involution. The
pair already contains `ab`, so the checked identities give both generators.
Only zero and the exact published exception list are excluded.

Source: primary ATLAS Tits generators; see `GenericGeneration/source/README.md`.
Untrusted word discovery: `source/discover.py`; certificate emission: `source/emit.py`.
-/

namespace Tits.MinimumIndexThirteen.PairGeneration.GenericGeneration

private def words (i : Fin 32) : List (Bool × Int) :=
  if i.val < 16 then
    if i.val < 8 then
      if i.val < 4 then
        if i.val < 2 then
          if i.val < 1 then
            [(false, 5), (true, -5), (false, -4), (true, 2), (false, -3), (true, -3), (false, 4)]
          else
            [(true, 5), (false, 2), (true, 3), (false, 6), (true, 3), (false, -4), (true, 5)]
        else
          if i.val < 3 then
            [(false, -6), (true, 1), (false, 5), (true, -3), (false, -6), (true, 3), (false, 5)]
          else
            [(false, 6), (true, 6), (false, -2), (true, -5), (false, -2), (true, -4), (false, -2)]
      else
        if i.val < 6 then
          if i.val < 5 then
            [(false, -1), (true, -3), (false, -1), (true, 5), (false, 4), (true, 4), (false, -5), (true, 4)]
          else
            [(true, -5), (false, -2), (true, 3), (false, 6), (true, -6), (false, -6), (true, -2)]
        else
          if i.val < 7 then
            [(false, -6), (true, -5), (false, 4), (true, -1), (false, -4), (true, 5), (false, 4)]
          else
            [(false, -1), (true, 2), (false, 1), (true, 5), (false, -1), (true, 2), (false, -3), (true, 1)]
    else
      if i.val < 12 then
        if i.val < 10 then
          if i.val < 9 then
            [(false, 3), (true, -6), (false, 6), (true, -3), (false, 6), (true, 3), (false, -3)]
          else
            [(false, 3), (true, 6), (false, 2), (true, -5), (false, 5), (true, -6), (false, -1)]
        else
          if i.val < 11 then
            [(false, -1), (true, -2), (false, -2), (true, -4), (false, -6), (true, 2), (false, -2), (true, -4)]
          else
            [(false, -4), (true, -1), (false, 6), (true, -2), (false, 3), (true, 4)]
      else
        if i.val < 14 then
          if i.val < 13 then
            [(true, 2), (false, -2), (true, -5), (false, 2), (true, 3), (false, 6), (true, 1)]
          else
            [(false, 1), (true, -5), (false, 1), (true, -5), (false, -5), (true, -4), (false, 5), (true, -4)]
        else
          if i.val < 15 then
            [(false, -6), (true, 1), (false, 1), (true, 2), (false, 2), (true, -1), (false, -5)]
          else
            [(false, 3), (true, -2), (false, -5), (true, -5), (false, -6), (true, -1)]
  else
    if i.val < 24 then
      if i.val < 20 then
        if i.val < 18 then
          if i.val < 17 then
            [(true, 2), (false, -1), (true, 3), (false, -5), (true, 4), (false, 6), (true, 2)]
          else
            [(true, 3), (false, 2), (true, 6), (false, 2), (true, -3), (false, 4), (true, 1)]
        else
          if i.val < 19 then
            [(false, 6), (true, -6), (false, 2), (true, 5), (false, -3), (true, -1), (false, 5)]
          else
            [(true, 2), (false, 6), (true, -4), (false, 3), (true, 2), (false, -1), (true, -2)]
      else
        if i.val < 22 then
          if i.val < 21 then
            [(false, -3), (true, 5), (false, -3), (true, 5), (false, 3), (true, 4), (false, 3)]
          else
            [(false, 1), (true, 6), (false, -5), (true, -4), (false, 5), (true, -6), (false, 1)]
        else
          if i.val < 23 then
            [(false, -2), (true, -2), (false, 5), (true, 2), (false, -1), (true, 1), (false, -1)]
          else
            [(false, -4), (true, -3), (false, 5), (true, -4), (false, 3), (true, 4)]
    else
      if i.val < 28 then
        if i.val < 26 then
          if i.val < 25 then
            [(false, 5), (true, 1), (false, -6), (true, 6), (false, 3), (true, -1), (false, 5)]
          else
            [(false, 2), (true, 5), (false, 4), (true, 1), (false, 1), (true, 3)]
        else
          if i.val < 27 then
            [(false, -6), (true, 1), (false, -5), (true, 1), (false, -6), (true, -3), (false, -1)]
          else
            [(false, -3), (true, 4), (false, -4), (true, 4), (false, 2), (true, 6)]
      else
        if i.val < 30 then
          if i.val < 29 then
            [(false, 5), (true, 2), (false, 1), (true, 3), (false, -2), (true, -2), (false, -2)]
          else
            [(false, -6), (true, -3), (false, 3), (true, 6), (false, 2), (true, -2), (false, -4)]
        else
          if i.val < 31 then
            [(false, -1), (true, -5), (false, -6), (true, -5), (false, -1), (true, -2), (false, 2), (true, 4)]
          else
            [(false, 4), (true, -6), (false, -1), (true, 3), (false, -5), (true, -4), (false, 1)]

set_option maxRecDepth 20000 in
private theorem checked : blockTest 2016 32 words = true := by
  decide +kernel

/-- Every nonexcluded representative in this interval generates the whole carrier. -/
public theorem generation_2016_2048 (k : Fin 3010)
    (hlo : 2016 ≤ k.val) (hhi : k.val < 2048)
    (hk : k ≠ 0) (he : k ∉ exceptionalIndices) :
    pairSubgroup (representative k) = ⊤ :=
  blockTest_sound 2016 32 words checked k hlo hhi hk he

end Tits.MinimumIndexThirteen.PairGeneration.GenericGeneration
