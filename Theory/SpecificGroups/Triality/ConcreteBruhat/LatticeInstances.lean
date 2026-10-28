module

public import Theory.SpecificGroups.Triality.LeviRankOneMatrices.Coordinates

/-!
# Common equality on the triality Geck lattice

The torus and Weyl matrix calculations use the same Cartan-plus-root basis.
They share this decidable equality so that their exported declarations can be
imported together. The instance is activated locally by those calculations.
-/

@[expose] public section
noncomputable section
namespace Triality.Standard.ConcreteBruhat
open Parabolics.RankOneMatrices

local instance : DecidableEq LatticeIndex := fun a b => instDecidableEqSum a b

end Triality.Standard.ConcreteBruhat
