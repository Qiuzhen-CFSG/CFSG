module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Geometry.SchreierData
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Geometry.Edges.Checks

/-!
# Certified four-point Schreier edges for the literal J₂ cosets

Every one of the 24192 fixed candidate rows satisfies the required generator
edge equation at all four base points and for all four letters. The proof
uses cached integer maps, proved equal to the unchanged original tables,
then 189 bounded kernel checks. In particular letter 2 is checked with its
actual permutation, even though its action and power tables repeat letter 0.

The final definition applies the existing four-point carrier criterion to
produce the actual `SchreierCertificate`. No BFS-word membership assertion,
orbit-reachability premise, or assumed group-order calculation is introduced.
The parent geometry construction consumes this certificate together with its
independent orbit certificate.

Source and conventions: Geometry/source/README.md, Coordinates/source/README.md
and Presentation/source/README.md. Cached data reproduction and measurements:
Geometry/Edges/source/README.md.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Geometry

/-- All fixed generator edges agree on the certified four-point base. -/
theorem edgeChecks : EdgeChecks := by
  intro x l j
  apply Edges.edge_of_raw x l j
  have hblock : x.val / 128 < 189 := by omega
  have h := Edges.checkBlock_sound (x.val / 128)
    (Edges.allBlocks ⟨x.val / 128, hblock⟩)
    ⟨x.val % 128, Nat.mod_lt _ (by decide)⟩ l j
  simpa only [Fin.val_mk, Nat.div_add_mod] using h

/-- The actual-carrier Schreier input for the literal right-coset geometry. -/
def schreierCertificate : SchreierCertificate :=
  schreierCertificate_of_edgeChecks edgeChecks

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Geometry
