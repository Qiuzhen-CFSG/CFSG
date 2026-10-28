module

public import Theory.AtlasPort.Janko2.Conway.IcosianProjectiveModel
public import Theory.AtlasPort.Janko2.Conway.IcosianReflectionDiagonalData
public import Theory.AtlasPort.Janko2.Conway.IcosianAxisTransitionData

/-!
# A concrete pair in the projective icosian group

Both elements are images of words of length four in integral root reflections.
The cover words use the actual Hermitian lattice group; the projection divides
out exactly its two central signs. Products act on the rightmost vector first.

The root coordinates and their lattice certificates are Gerald Höhn's ATLAS
construction, with attribution and license retained in the imported modules.
The target relations are ATLAS `J2G1-P2`. This module defines the pair without
asserting its relations or generation.
-/

@[expose] public section

namespace Sporadic.LeechRelated.J2.IcosianComparison.Generators
open Atlas.Conway

noncomputable def xLift : icosianHermitianGroup :=
  icosianAxisTransitionGenerator 1 * icosianReflectionDiagonalGenerator 2 *
    icosianAxisTransitionGenerator 3 * icosianReflectionDiagonalGenerator 1

noncomputable def yLift : icosianHermitianGroup :=
  icosianReflectionDiagonalGenerator 1 * icosianAxisTransitionGenerator 0 *
    icosianAxisTransitionGenerator 3 * icosianAxisTransitionGenerator 0

noncomputable def x : IcosianProjectiveModel := icosianProjectiveProjection xLift

noncomputable def y : IcosianProjectiveModel := icosianProjectiveProjection yLift

end Sporadic.LeechRelated.J2.IcosianComparison.Generators
