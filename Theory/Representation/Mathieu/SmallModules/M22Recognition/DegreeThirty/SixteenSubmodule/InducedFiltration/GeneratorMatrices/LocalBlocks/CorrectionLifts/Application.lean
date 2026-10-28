module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.GeneratorMatrices.LocalBlocks
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.GeneratorMatrices.LocalBlocks.CorrectionLifts

/-!
# Applying the explicit correction lifts to native binary blocks

The 44 certified lifts discharge the literal pair-embedding premise of
`correction_blocks_of_pair_lifts`. The remaining premise is exactly the
independent calculation of binary adjoint coordinates for the executable
matrices. No alternative group marking is introduced.

Source context: Guralnick--Malle I, Proposition 5.1, pp.15--16;
Aschbacher--Smith, Chapter K, printed pp.451--452 and 457.
-/

public section
open Sporadic.Mathieu MathieuCode
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.LocalBlocks

/-- The correction-lift certificates discharge the pair-lift premise of the native block theorem.
Only the independent binary-coordinate calculation remains explicit. -/
theorem correction_blocks_of_matrices
    (e : Adjoint ≃ₗ[ZMod 2] (Fin 16 → ZMod 2))
    (blocks : Fin 2 → Fin 22 → Matrix (Fin 16) (Fin 16) (ZMod 2))
    (hblocks : ∀ k i v,
      e (adjointBinary (Matrix.SpecialLinearGroup.map
        M23Geometry.PairPlaneCoordinates.fieldEquiv.toRingHom (correctionMatrix k i)) v) =
          (blocks k i).mulVec (e v)) (k : Fin 2) (i : Fin 22) (v : Adjoint) :
    nativeCoordinates e (pointAdjoint (GeneratorMatrices.generatorCorrection k i) v) =
      (blocks k i).mulVec (nativeCoordinates e v) := by
  apply correction_blocks_of_pair_lifts e correctionLift blocks correctionLift_embedding
    (fun k i v => ?_) k i v
  rw [correctionLift_pointwiseEquiv, projectiveAdjoint_mk]
  exact hblocks k i v

end Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.LocalBlocks
