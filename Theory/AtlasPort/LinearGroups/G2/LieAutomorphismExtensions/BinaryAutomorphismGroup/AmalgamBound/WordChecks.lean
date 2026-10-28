module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.Data

/-!
# Kernel checks for the binary amalgam word tables

Every row is recovered by its positive word in rows 1 and 2. The displayed
relators hold, row 1 has nonidentity fourth power, and it is the same numbered
overlap row on both sides. These checks supply the finite identities used by
the automorphism sieve; comparison with actual G₂ subgroups remains separate.

Source application: Aschbacher--Smith F.1.12 and Definition F.4.3; root
coordinate provenance and the reproducible generator are recorded in `Data`.
-/

@[expose] public section
namespace Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound

theorem left_valid : leftTable.Valid := by
  constructor <;> decide +kernel

theorem right_valid : rightTable.Valid := by
  constructor <;> decide +kernel

end Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound
