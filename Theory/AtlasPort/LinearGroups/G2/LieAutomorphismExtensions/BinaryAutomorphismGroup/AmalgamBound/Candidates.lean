module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.Data

/-!
# Candidate images of the three generators of the binary amalgam

One overlap element and the cubic in each parabolic determine an amalgam
automorphism. The local relators, exact order of the overlap generator, and
preservation of the whole overlap give finite necessary conditions. The last
condition compares both local images at every overlap row, using their common
ambient matrix labels. No extension to a global automorphism is assumed.

Source application: Aschbacher--Smith F.1.12 and Definition F.4.3.
-/

@[expose] public section
namespace Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound

abbrev Compatible := leftTable.Compatible rightTable

/-- The purely finite sieve; bounding this type needs no abstract-group enumeration. -/
abbrev Candidate := {s : Signature // Compatible s}

end Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound
