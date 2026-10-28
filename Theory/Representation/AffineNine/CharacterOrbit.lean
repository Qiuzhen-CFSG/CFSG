module

public import Theory.Representation.AffineNine.UniformWeights
public meta import Mathlib.Data.Matrix.Basic
public meta import Mathlib.Data.ZMod.Defs
public meta import Mathlib.Algebra.GroupWithZero.Units.Fintype
public meta import Mathlib.Algebra.Field.ZMod
public meta import Theory.Representation.AffineNine.Model

open Matrix
open scoped MatrixGroups

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

public section

namespace Representation.AffineNine

/- The following eight determinant-one matrices are a small orbit certificate.
   Keeping the certificate explicit lets the kernel check the finite orbit
   calculation without introducing a native-evaluation axiom. -/
private def orbit0 : SpecialLinear := ⟨!![1, 0; 0, 1], by decide⟩
private def orbit1 : SpecialLinear := ⟨!![0, 1; 2, 0], by decide⟩
private def orbit2 : SpecialLinear := ⟨!![2, 0; 0, 2], by decide⟩
private def orbit3 : SpecialLinear := ⟨!![0, 2; 1, 0], by decide⟩
private def orbit4 : SpecialLinear := ⟨!![1, 2; 2, 2], by decide⟩
private def orbit5 : SpecialLinear := ⟨!![2, 2; 2, 1], by decide⟩
private def orbit6 : SpecialLinear := ⟨!![1, 1; 1, 2], by decide⟩
private def orbit7 : SpecialLinear := ⟨!![2, 1; 1, 1], by decide⟩

private def orbitCertificate : List SpecialLinear :=
  [orbit0, orbit1, orbit2, orbit3, orbit4, orbit5, orbit6, orbit7]

/-- The natural `GL₂(3)` action is transitive on the eight nonzero vectors of
the ternary plane.  This is the finite model calculation for the dual
character action. -/
public theorem dualPerm_full_transitive (w z : Plane) (hw : w ≠ 0) (hz : z ≠ 0) :
    ∃ g : LinearGroup, dualPerm g w = z := by
  obtain ⟨g, hg, hgz⟩ : ∃ g ∈ orbitCertificate,
      dualPerm (SpecialLinearGroup.toGL g) w = z := by
    decide +revert
  exact ⟨SpecialLinearGroup.toGL g, hgz⟩

/-- The natural `SL₂(3)` action is already transitive on the eight nonzero
vectors of the ternary plane. -/
public theorem dualPerm_special_transitive (w z : Plane) (hw : w ≠ 0) (hz : z ≠ 0) :
    ∃ g : SpecialLinear, dualPerm (SpecialLinearGroup.toGL g) w = z := by
  obtain ⟨g, hg, hgz⟩ : ∃ g ∈ orbitCertificate,
      dualPerm (SpecialLinearGroup.toGL g) w = z := by
    decide +revert
  exact ⟨g, hgz⟩

end Representation.AffineNine
