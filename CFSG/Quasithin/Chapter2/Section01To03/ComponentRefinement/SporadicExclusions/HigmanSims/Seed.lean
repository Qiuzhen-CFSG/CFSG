module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.HigmanSims.Reduction
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.Interface

/-!
# Inputs for transporting the HS normalizer geometry

The intrinsic contracts live with the exact permutation carrier and may also
be used by the local-generation arguments of Chapter E. These aliases connect
them to the central-cover and component-orbit transport needed for
Aschbacher–Smith 2.3.9(7), printed p.526. Neither the concrete geometry nor
its transport to `LocalGeometry` is asserted here.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.HigmanSims

/-- The intrinsic normalizer seed, with its actual quotient and action. -/
abbrev IntrinsicLocalSeed := Sporadic.LeechRelated.HS.BlockNormalizer.LocalSeed

/-- The remaining intrinsic geometry, shared with other HS local arguments. -/
abbrev IntrinsicGeometry := Sporadic.LeechRelated.HS.BlockNormalizer.Geometry

end CFSG.Quasithin.Chapter2.ComponentRefinement.HigmanSims
