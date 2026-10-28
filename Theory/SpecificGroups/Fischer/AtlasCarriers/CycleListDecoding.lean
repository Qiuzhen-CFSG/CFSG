module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.CycleEncoding

/-!
# A reducible character-list decoder for cycle certificates

The public equations for `List.splitOn` identify it with this exposed recursive
splitter. This permits kernel computation in certificate modules even though
the implementation bodies of the core list splitter are private. The decimal
decoder and resulting permutation are unchanged.

Used for the ATLAS Fischer cycle tables; see `CycleEncoding` for attribution.
-/

@[expose] public section
namespace Sporadic.Fischer.AtlasCarriers

/-- The accumulator recurrence from the public specification of `List.splitOn`. -/
def splitCycleChars (sep : Char) : List Char → List Char → List (List Char)
  | [], acc => [acc.reverse]
  | c :: cs, acc =>
    if c == sep then acc.reverse :: splitCycleChars sep cs []
    else splitCycleChars sep cs (c :: acc)

private theorem splitCycleChars_spec (sep : Char) (cs acc : List Char) :
    splitCycleChars sep cs acc = List.splitOnPPrepend (· == sep) cs acc := by
  induction cs generalizing acc with
  | nil => simp only [splitCycleChars, List.splitOnPPrepend_nil]
  | cons c cs ih =>
    rw [splitCycleChars, List.splitOnPPrepend_cons_eq_if]
    split <;> simp only [ih, List.splitOnPPrepend_nil_right]

theorem splitOn_eq_splitCycleChars (sep : Char) (cs : List Char) :
    cs.splitOn sep = splitCycleChars sep cs [] := by
  rw [List.splitOn_eq_splitOnP, List.splitOnP_eq_splitOnPPrepend,
    splitCycleChars_spec]

end Sporadic.Fischer.AtlasCarriers
