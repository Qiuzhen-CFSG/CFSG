module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.Coordinates
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Frames

/-!
# Assembly of the two concrete Leech local constructions

The SL₃(4) frame and the compatible marked short-root frame supply precisely
`LocalCoordinates`. Their finite single-coordinate tests extend to the indexed
equations by additivity. The two frames still require concrete constructions;
this module does not assert an unconditional inhabitant.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284.
The parent Leech-geometry assembly separately proves faithfulness of the action.
-/

public noncomputable section

namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators
open OctonionLocals

/-- Assemble the two actual local branches, extending their finite tests to
all vectors. All construction and marking premises remain explicit. -/
def LongFrame.toLocalCoordinates (L : LongFrame) (S : ShortFrame L) : LocalCoordinates where
  long := L.long
  short := S.short
  swap := L.swap
  long_mem := L.long_mem
  short_mem := S.short_mem
  swap_mem := L.swap_mem
  coordinates := L.coordinates
  coordinates_injective := L.coordinates_injective
  coordinates_range := L.coordinates_range
  on_generators := by
    rintro ((A | a) | i) v
    · exact equivariant_of_single _ _ _ (L.on_long A) v
    · exact equivariant_of_single _ _ _ (S.on_short a) v
    · exact equivariant_of_single _ _ _ L.on_swap v
  marked := S.marked

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators
