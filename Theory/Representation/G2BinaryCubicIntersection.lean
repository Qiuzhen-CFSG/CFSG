module
public import Theory.Representation.G2BinaryParabolicFrame
public import Theory.Representation.G2BinaryPointFlagDisplacement

/-!
# The cubic conjugate of the marked binary three-space

The third basis vector of the marked seed pairs nontrivially with its
image under the plane cubic. Thus the join of the seed and that cubic
conjugate is not totally isotropic. This is the unitary geometry needed
in Aschbacher--Smith 13.3.14(b), printed p.891. The root action and its
ATLAS attribution are inherited from the imported split-octonion model.
-/

public section
namespace Atlas.G2.Natural.BinaryPointFlag
open Atlas.G2.BinaryParabolicPair

/-- A literal pairing witnesses nonisotropy of the joined three-spaces. -/
theorem pairing_plane_cubic_seed : pairing (Pi.single 2 1)
    (Restricted.NaturalCoordinates.action F cubicActor (Pi.single 2 1)) = 1 := by
  simp [pairing_apply,cubicActor,shortRoot,map_mul,Module.End.mul_apply]

end Atlas.G2.Natural.BinaryPointFlag
