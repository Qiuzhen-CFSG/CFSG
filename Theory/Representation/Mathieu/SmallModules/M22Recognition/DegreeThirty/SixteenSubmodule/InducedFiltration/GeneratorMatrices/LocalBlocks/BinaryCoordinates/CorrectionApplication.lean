module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.GeneratorMatrices.LocalBlocks.BinaryCoordinates
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.GeneratorMatrices.LocalBlocks

/-!
# Applying binary adjoint coordinates to the correction family

The explicit binary matrix rule supplies the coefficient premise of
`correction_blocks_of_pair_lifts`. The remaining inputs are the actual pair
lifts of the 44 corrections and their projective matrix identifications.
Their certificates belong to the correction-family assembly.

Source context: Guralnick--Malle I, Proposition 5.1, pp.15--16;
Aschbacher--Smith, Chapter K, printed pp.451--452 and 457.
-/

public section
open Sporadic.Mathieu MathieuCode
open M23Geometry.PairPlaneCoordinates
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.LocalBlocks

/-- The executable matrices give the native blocks once the literal pair lifts
and their projective identifications have been certified. This discharges the
binary-coordinate premise of `correction_blocks_of_pair_lifts`. -/
theorem correction_blocks_of_binary_lifts
    (lifts : Fin 2 → Fin 22 → M23Geometry.pointwisePairStabilizer)
    (matrices : Fin 2 → Fin 22 → Matrix.SpecialLinearGroup (Fin 3) Four)
    (hlifts : ∀ k i, pairEmbedding (lifts k i) = explicitMarking *
      m22Embedding (GeneratorMatrices.generatorCorrection k i).val * explicitMarking⁻¹)
    (hmatrices : ∀ k i, M23Geometry.PairPlane.pointwiseEquiv (lifts k i) =
      (Matrix.SpecialLinearGroup.map fieldEquiv.toRingHom (matrices k i) :
        Matrix.PSL3Four.PSL))
    (k : Fin 2) (i : Fin 22) (v : Adjoint) :
    nativeCoordinates binaryCoordinates
      (pointAdjoint (GeneratorMatrices.generatorCorrection k i) v) =
      (binaryMatrix (matrices k i)).mulVec (nativeCoordinates binaryCoordinates v) := by
  apply correction_blocks_of_pair_lifts binaryCoordinates lifts
    (fun k i => binaryMatrix (matrices k i)) hlifts
  intro k i v
  rw [hmatrices, projectiveAdjoint_mk]
  exact binaryCoordinates_intertwines (matrices k i) v

end Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.LocalBlocks
