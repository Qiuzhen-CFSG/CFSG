module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.FullTwists.Actual.Left
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.FullTwists.Actual.Right

/-!
# Both literal overlap maps for the full binary G₂ tables

The labels of the left and right overlap rows agree. The left overlap map is
injective and preserves the published middle multiplication. Together with
the actual endpoint word actions, these certificates realize the entire
common Sylow subgroup and both inclusion squares in `FullTwists.Actual`.

Source application: Aschbacher--Smith F.1.12(I)(3), q = 2, pp.262--263.
Coordinates: Gerald Höhn and the ATLAS contributors, ATLAS Research and
Attribution License 1.0 (`LICENSES/ATLAS.txt`).
-/

public section
namespace Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound.FullTwists.Actual
set_option maxRecDepth 4096
set_option Elab.async false

theorem overlap_labels : ∀ i,
    leftLabel (leftOverlap i) = rightLabel (rightOverlap i) := by
  decide +kernel

theorem left_overlap_injective : Function.Injective leftOverlap := by
  decide +kernel

theorem left_overlap_mul : ∀ i j,
    leftOverlap (middleMul i j) = leftMul (leftOverlap i) (leftOverlap j) := by
  decide +kernel

end Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound.FullTwists.Actual
