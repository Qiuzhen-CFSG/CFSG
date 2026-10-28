module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.WordsTwentyToTwentySix.Relations

/-!
# Certified shortening of the six literal inverse words

The comparisons below rewrite the literal reverse-inverse walks using the
raw-table identities proved in Relations. They preserve all 25 power pairs
and the original left-then-right subgroup actions. The short column is only a
computational refinement of the exact wordColumn definition.

Source: Columns/Catalogue.lean and Columns/source/README.md.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.Columns.WordsTwentyToTwentySix

/-- The XOR computation for an already inverted word, retaining every term. -/
def shortColumn (w : List (Fin 4)) (j : Fin 1008) : Nat :=
  xorList (List.ofFn fun u : Fin 5 => xorList (List.ofFn fun v : Fin 5 =>
    2 ^ (fastOrbit (fastWalk w (subgroupPoint leftAction rightAction (u,v) j))).val))

def inverse20 : List (Fin 4) := [0, 3]

theorem inverse_walk_20 (x : Point) :
    fastWalk (inverseWord (words 20)) x = fastWalk inverse20 x := by
  change fastWalk [1, 3, 3, 2, 2, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 3, 1, 3] x = fastWalk inverse20 x
  simp only [fastWalk, inverse20, List.foldl_cons, List.foldl_nil,
    step_two, step_zero_zero, step_one_three, step_three_one]

theorem wordColumn_20_eq (j : Fin 1008) :
    wordColumn leftAction rightAction (words 20) j = shortColumn inverse20 j := by
  unfold wordColumn shortColumn
  simp only [inverse_walk_20]

def inverse21 : List (Fin 4) := [3, 0, 1]

theorem inverse_walk_21 (x : Point) :
    fastWalk (inverseWord (words 21)) x = fastWalk inverse21 x := by
  change fastWalk [1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 3, 2, 1, 3, 2] x = fastWalk inverse21 x
  simp only [fastWalk, inverse21, List.foldl_cons, List.foldl_nil,
    step_two, step_zero_zero, step_one_three, step_three_one, step_one_one, step_three_three]

theorem wordColumn_21_eq (j : Fin 1008) :
    wordColumn leftAction rightAction (words 21) j = shortColumn inverse21 j := by
  unfold wordColumn shortColumn
  simp only [inverse_walk_21]

def inverse22 : List (Fin 4) := [0, 3, 0, 1, 0, 3, 0]

theorem inverse_walk_22 (x : Point) :
    fastWalk (inverseWord (words 22)) x = fastWalk inverse22 x := by
  change fastWalk [2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 2, 3, 1, 2, 2, 3, 2] x = fastWalk inverse22 x
  simp only [fastWalk, inverse22, List.foldl_cons, List.foldl_nil,
    step_two, step_zero_zero, step_one_three, step_three_one, step_one_one]

theorem wordColumn_22_eq (j : Fin 1008) :
    wordColumn leftAction rightAction (words 22) j = shortColumn inverse22 j := by
  unfold wordColumn shortColumn
  simp only [inverse_walk_22]

def inverse23 : List (Fin 4) := [0, 3, 0, 1, 0, 1, 0, 1]

theorem inverse_walk_23 (x : Point) :
    fastWalk (inverseWord (words 23)) x = fastWalk inverse23 x := by
  change fastWalk [2, 3, 2, 3, 3, 3, 3, 3, 1, 3, 2, 3, 2, 2, 3, 1, 3, 2, 3, 3] x = fastWalk inverse23 x
  simp only [fastWalk, inverse23, List.foldl_cons, List.foldl_nil,
    step_two, step_zero_zero, step_three_one, step_one_one, step_three_three]

theorem wordColumn_23_eq (j : Fin 1008) :
    wordColumn leftAction rightAction (words 23) j = shortColumn inverse23 j := by
  unfold wordColumn shortColumn
  simp only [inverse_walk_23]

def inverse24 : List (Fin 4) := [0, 1, 0, 1, 0, 3, 0]

theorem inverse_walk_24 (x : Point) :
    fastWalk (inverseWord (words 24)) x = fastWalk inverse24 x := by
  change fastWalk [2, 3, 3, 3, 1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 3, 2] x = fastWalk inverse24 x
  simp only [fastWalk, inverse24, List.foldl_cons, List.foldl_nil,
    step_two, step_zero_zero, step_one_three, step_three_one, step_one_one, step_three_three]

theorem wordColumn_24_eq (j : Fin 1008) :
    wordColumn leftAction rightAction (words 24) j = shortColumn inverse24 j := by
  unfold wordColumn shortColumn
  simp only [inverse_walk_24]

def inverse25 : List (Fin 4) := [3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0]

theorem inverse_walk_25 (x : Point) :
    fastWalk (inverseWord (words 25)) x = fastWalk inverse25 x := by
  change fastWalk [1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 2, 1, 2, 1, 1, 3, 1, 2, 3, 2] x = fastWalk inverse25 x
  simp only [fastWalk, inverse25, List.foldl_cons, List.foldl_nil,
    step_two, step_three_one, step_one_one, step_three_three]

theorem wordColumn_25_eq (j : Fin 1008) :
    wordColumn leftAction rightAction (words 25) j = shortColumn inverse25 j := by
  unfold wordColumn shortColumn
  simp only [inverse_walk_25]

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.Columns.WordsTwentyToTwentySix
