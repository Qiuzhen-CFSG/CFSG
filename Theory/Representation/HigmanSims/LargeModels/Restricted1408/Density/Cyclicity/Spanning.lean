module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.Spanning.Row00
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.Spanning.Row01
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.Spanning.Row02
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.Spanning.Row03
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.Spanning.Row04
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.Spanning.Row05
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.Spanning.Row06
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.Spanning.Row07
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.Spanning.Row08
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.Spanning.Row09
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.Spanning.Row10
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.Spanning.Column00
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.Spanning.Column01
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.Spanning.Column02
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.Spanning.Column03
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.Spanning.Column04
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.Spanning.Column05
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.Spanning.Column06
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.Spanning.Column07
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.Spanning.Column08
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.Spanning.Column09
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.Spanning.Column10

/-!
# Spanning of both literal degree-1408 cyclic orbit tables

For each coordinate, an explicit binary combination of the published orbit
rows equals its coordinate power of two. Kernel-checked inverse blocks cover
all 1408 coordinates; the balanced checker is proved equivalent to the exact
`PackedBinaryRows.listProduct` used by `PackedSpanning`.

No action recurrence, kernel dimension, or density hypothesis enters these
arithmetic theorems. The cyclicity assembly consumes them together with the
separate row and column recurrence certificates. See `Spanning/source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity
open Spanning

/-- Every coordinate vector is a binary combination of the published row orbit. -/
theorem rowOrbit_spanning : PackedSpanning rowOrbitRows :=
  packedSpanning_of_covers rowOrbitRows (((rowBlock00.append rowBlock01).append (rowBlock02.append (rowBlock03.append rowBlock04))).append ((rowBlock05.append (rowBlock06.append rowBlock07)).append (rowBlock08.append (rowBlock09.append rowBlock10))))

/-- Every coordinate vector is a binary combination of the published column orbit. -/
theorem columnOrbit_spanning : PackedSpanning columnOrbitRows :=
  packedSpanning_of_covers columnOrbitRows (((columnBlock00.append columnBlock01).append (columnBlock02.append (columnBlock03.append columnBlock04))).append ((columnBlock05.append (columnBlock06.append columnBlock07)).append (columnBlock08.append (columnBlock09.append columnBlock10))))

end Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity
