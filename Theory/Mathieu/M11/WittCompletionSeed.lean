module

public import Theory.GroupTheory.SteinerSystem
public import Mathlib.Data.Fin.Basic

/-!
# The four-block normalization seed for the small Witt design

The blocks through a triple in an `S(4,5,11)` partition the other eight points
into pairs. Labeling the triple by `0,1,2` and the pairs consecutively gives
the following seed. This definition specifies a labeling convention; it does
not replace or alter the explicit ATLAS model in `M11.Block`.
-/

namespace Sporadic.Mathieu

/-- The four blocks through the normalized triple `{0,1,2}`. -/
@[expose]
public def m11CompletionSeed : Finset (Finset (Fin 11)) :=
  {{0, 1, 2, 3, 4}, {0, 1, 2, 5, 6}, {0, 1, 2, 7, 8}, {0, 1, 2, 9, 10}}

end Sporadic.Mathieu
