module

public import GorensteinWalter.Section3.FirstCaseCountData

/-!
# The restated first-case involution count

This module owns the restated `firstCase_involutionCount`.  It takes the
Klein-four hypothesis `hklein : IsKleinFour (pCore 2 c.Hhat)` directly
instead of the `FirstCase c` predicate, and it is independent of every other
Section 3 module: the counting content is supplied by `FirstCaseCountData`
and the arithmetic consumer in `FirstCaseCountData.lean`.
-/

noncomputable section

namespace GorensteinWalter

universe u

/-- The involution count in Section 3 gives index `35` and the order of
`A₇`.  The `FirstCaseCountData` argument is the package containing Bender's
identities (1)--(9) and the derived numerical facts. -/
public theorem firstCase_involutionCount
    {G : Type u} [Group G] [Finite G]
    (_hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    (d : FirstCaseCountData c) :
    c.Hhat.index = 35 ∧ Nat.card G = 2 ^ 3 * 3 ^ 2 * 5 * 7 := by
  have _ := hklein
  exact firstCase_index_card_of_countData c d

end GorensteinWalter
