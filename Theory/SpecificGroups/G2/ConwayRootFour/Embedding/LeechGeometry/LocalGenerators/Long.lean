module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Frames
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Setup
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup

/-!
# The long Leech frame

The concrete integral block and graph normalizer descend to the Leech central
quotient, and conjugacy of tetrahedral scalar markings places their local group
in the literal `centralizerI`. Its faithful action on the U-fixed space contains
the natural SL₃(4) module; adjoining its graph translate supplies the natural
plus dual coordinates with the prescribed block and graph conventions.

`nonempty_longFrame` joins these two constructions without additional premises.
The coordinates are additive and injective, and the proved fixed-space dimension
bound identifies their image with the entire literal U-fixed space. This is the
long local input to `LongFrame.toLocalCoordinates`; the compatible short frame
remains the other input to that assembly.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284.
-/

namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators

/-- The actual SL₃(4) block and graph element in the tetrahedral Leech
centralizer admit all six prescribed coordinates on the literal U-fixed space. -/
public theorem nonempty_longFrame : Nonempty LongFrame := by
  obtain ⟨E⟩ := Long.nonempty_localEmbedding
  exact Long.nonempty_longFrame_of_localEmbedding E

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators
