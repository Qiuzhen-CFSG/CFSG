module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.GeneratorMatrices.LocalBlocks.Marking
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.GeneratorMatrices.LocalBlocks.BinaryCoordinates
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.GeneratorMatrices.LocalBlocks.CorrectionLifts

/-!
# The 44 executable blocks of the native binary adjoint

The explicit M24 marking has a proved, uniform comparison with the native
chosen marking. Composing that comparison with the explicit trace-zero binary
coordinates gives one equivalence `coordinates` for all 44 generator corrections.
The certified transvection words yield determinant-one matrices over the
executable quadratic field; `blocks` computes their conjugation on the sixteen
explicit binary coordinate vectors. The theorem `correction_blocks` proves the
local identity with no remaining certificate or coordinate hypotheses.

The general certificate connection is retained for reuse. The 352-dimensional
sparse matrix assembly remains in `GeneratorMatrices`; this module imports only
its transversal layer through `Marking`, avoiding an assembly cycle.

Source context: Guralnick--Malle I, Proposition 5.1, pp.15--16;
Aschbacher--Smith, Chapter K, printed pp.451--452 and 457.
-/

@[expose] public section
open Sporadic.Mathieu MathieuCode
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.LocalBlocks

/-- Apply the proved native marking comparison before reading binary coordinates. -/
noncomputable def nativeCoordinates (e : Adjoint ≃ₗ[ZMod 2] (Fin 16 → ZMod 2)) :
    Adjoint ≃ₗ[ZMod 2] (Fin 16 → ZMod 2) := markingChange.trans e

/-- Pair-lift and coefficient certificates imply the literal native correction identity.
Both families of certificates must be constructed before obtaining numerical blocks. -/
theorem correction_blocks_of_pair_lifts
    (e : Adjoint ≃ₗ[ZMod 2] (Fin 16 → ZMod 2))
    (lifts : Fin 2 → Fin 22 → M23Geometry.pointwisePairStabilizer)
    (blocks : Fin 2 → Fin 22 → Matrix (Fin 16) (Fin 16) (ZMod 2))
    (hlifts : ∀ k i, pairEmbedding (lifts k i) = explicitMarking *
      m22Embedding (GeneratorMatrices.generatorCorrection k i).val * explicitMarking⁻¹)
    (hblocks : ∀ k i v,
      e (projectiveAdjoint (M23Geometry.PairPlane.pointwiseEquiv (lifts k i)) v) =
        (blocks k i).mulVec (e v)) (k : Fin 2) (i : Fin 22) (v : Adjoint) :
    nativeCoordinates e (pointAdjoint (GeneratorMatrices.generatorCorrection k i) v) =
      (blocks k i).mulVec (nativeCoordinates e v) := by
  change e (markingChange (pointAdjoint (GeneratorMatrices.generatorCorrection k i) v)) = _
  rw [markingChange_intertwines _ _ (hlifts k i), hblocks]
  rfl

/-- One binary coordinate equivalence for every native stabilizer correction. -/
noncomputable def coordinates : Adjoint ≃ₗ[ZMod 2] (Fin 16 → ZMod 2) :=
  nativeCoordinates binaryCoordinates

/-- The executable sixteen-by-sixteen blocks for both generators at all 22 points. -/
def blocks (k : Fin 2) (i : Fin 22) : Matrix (Fin 16) (Fin 16) (ZMod 2) :=
  binaryMatrix (correctionMatrix k i)

/-- All 44 literal native corrections act by the executable blocks in the same coordinates.
This discharges the local identity required by the sparse induced-matrix assembly. -/
theorem correction_blocks (k : Fin 2) (i : Fin 22) (v : Adjoint) :
    coordinates (pointAdjoint (GeneratorMatrices.generatorCorrection k i) v) =
      (blocks k i).mulVec (coordinates v) := by
  apply correction_blocks_of_pair_lifts binaryCoordinates correctionLift blocks
    correctionLift_embedding
  intro k i v
  rw [correctionLift_pointwiseEquiv, projectiveAdjoint_mk]
  exact binaryCoordinates_intertwines (correctionMatrix k i) v

end Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.LocalBlocks
