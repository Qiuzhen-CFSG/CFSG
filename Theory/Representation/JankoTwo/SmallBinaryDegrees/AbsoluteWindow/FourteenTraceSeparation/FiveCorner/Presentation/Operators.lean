module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.OperatorData
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Transfer

/-!
# Binary orbit coordinates for the proposed Hall--Janko presentation

The row index is the input orbit and the column index is the output orbit,
as in GAP's right multiplication. The additive operator consequently acts by
`(T v) j = ∑ i, v i * row i j`. Coordinate zero is the identity double coset.
The two finite certificate contracts below assert neither the rank calculation
nor a relation; their independent producer must prove both. Their connection
to the literal corner is the separate `LiteralCoordinates` contract.

Source: the Hall--Janko five-corner discovery, described in source/README.md.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation

/-- Coordinates in the proposed ordered orbit-sum basis. -/
abbrev Coordinates := Fin 1008 → ZMod 2

/-- Packed right multiplication rows for the nine fixed generators. -/
def rows : Fin 9 → Array ℕ := ![rows0, rows1, rows2, rows3, rows4, rows5, rows6, rows7, rows8]

/-- Input orbit first, output orbit second. -/
def entry (k : Fin 9) (i j : Fin 1008) : ZMod 2 :=
  if ((rows k)[i.val]!).testBit j.val then 1 else 0

/-- The additive operation specified by the discovered rows. -/
def operator (k : Fin 9) : Coordinates →+ Coordinates where
  toFun v j := ∑ i : Fin 1008, v i * entry k i j
  map_zero' := by ext j; simp
  map_add' v w := by ext j; simp [add_mul, Finset.sum_add_distrib]

/-- The proposed coordinates of the actual corner identity e. -/
def seed : Coordinates := fun i => if i = 0 then 1 else 0

/-- The independent finite rank obligation: words in the nine operators span
all 1008 binary coordinates by finite sums. -/
def CoordinateWordSpan : Prop :=
  ∀ v : Coordinates, ∃ ws : List (List (Fin 9)),
    (ws.map (runWord (fun i => operator i) seed)).sum = v

/-- The independent finite polynomial obligation, using every unchanged
relation from the shared certificate. -/
def CoordinateRelations : Prop :=
  ∀ r ∈ Certificate.relations,
    runRelation (fun i => operator i) seed r = 0

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation
