module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.Models
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.GeneratorMatrices.LocalBlocks.Marking
import all Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.GeneratorMatrices.LocalBlocks.Marking
import all Theory.Representation.MathieuCodeRestriction.M22.SourceModules.OrbitStabilizers.Models

/-!
# The native marking change on the Hermitian nine-space

The explicit and chosen M24 markings differ by an element of the embedded
pointwise-pair subgroup. Apply the actual Hermitian representation to its PSL
image. This gives one coordinate change for every native stabilizer element,
and connects the shared correction lifts to Hermitian binary matrices.

The internal imports intentionally reuse the already proved marking-difference
identity. Public signatures use only the actual groups and representations;
the chosen difference and the body of `markingChange` remain private.

Source context: Guralnick--Malle I, Proposition 5.1, pp.15--16;
Aschbacher--Smith H.4.4 and Chapter K, printed pp.381,451--452,457.
-/

open Representation Sporadic.Mathieu
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.NativeComparison

open SixteenSubmodule.LocalBlocks

/-- Inner change from the native point marking to the explicit M24 marking. -/
public noncomputable def markingChange : Models.HermitianSpace ≃ₗ[ZMod 2]
    Models.HermitianSpace where
  toLinearMap := Models.hermitian changeElement
  invFun := Models.hermitian changeElement⁻¹
  left_inv := Models.hermitian.inv_self_apply changeElement
  right_inv := Models.hermitian.self_inv_apply changeElement

/-- A single Hermitian coordinate change works for the full point stabilizer. -/
public theorem markingChange_intertwines (h : Models.pointGroup)
    (s : M23Geometry.pointwisePairStabilizer)
    (hs : pairEmbedding s = explicitMarking * MathieuCode.m22Embedding h.val *
      explicitMarking⁻¹) (v : Models.HermitianSpace) :
    markingChange (Models.pointAction false h v) =
      Models.hermitian (M23Geometry.PairPlane.pointwiseEquiv s) (markingChange v) := by
  rw [nativePair_conjugate h s hs]
  simp only [M23Geometry.PairPlane.pointwiseEquiv.map_mul,
    M23Geometry.PairPlane.pointwiseEquiv.map_inv]
  change Models.hermitian changeElement
    (Models.hermitian (M23Geometry.PairPlane.pointwiseEquiv (MathieuCode.innerToM23 0 h)) v) =
      Models.hermitian (changeElement *
        M23Geometry.PairPlane.pointwiseEquiv (MathieuCode.innerToM23 0 h) * changeElement⁻¹)
        (Models.hermitian changeElement v)
  simp only [map_mul, Module.End.mul_apply, Representation.inv_self_apply]

/-- Native coordinates obtained from explicit-marking binary fiber coordinates. -/
@[expose] public noncomputable def nativeCoordinates
    (e : Models.HermitianSpace ≃ₗ[ZMod 2] (Fin 9 → ZMod 2)) :
    Models.HermitianSpace ≃ₗ[ZMod 2] (Fin 9 → ZMod 2) := markingChange.trans e

/-- The actual consumer of the shared pair-lift certificates and Hermitian
binary-coordinate rule. No abstract GAP stabilizer isomorphism is used. -/
public theorem correction_blocks_of_pair_lifts
    (e : Models.HermitianSpace ≃ₗ[ZMod 2] (Fin 9 → ZMod 2))
    (lifts : Fin 2 → Fin 22 → M23Geometry.pointwisePairStabilizer)
    (blocks : Fin 2 → Fin 22 → Matrix (Fin 9) (Fin 9) (ZMod 2))
    (hlifts : ∀ j i, pairEmbedding (lifts j i) = explicitMarking *
      MathieuCode.m22Embedding (SixteenSubmodule.GeneratorMatrices.generatorCorrection j i).val *
        explicitMarking⁻¹)
    (hblocks : ∀ j i v,
      e (Models.hermitian (M23Geometry.PairPlane.pointwiseEquiv (lifts j i)) v) =
        (blocks j i).mulVec (e v)) (j : Fin 2) (i : Fin 22) (v : Models.HermitianSpace) :
    nativeCoordinates e
      (Models.pointAction false (SixteenSubmodule.GeneratorMatrices.generatorCorrection j i) v) =
      (blocks j i).mulVec (nativeCoordinates e v) := by
  change e (markingChange (Models.pointAction false _ v)) = _
  rw [markingChange_intertwines _ _ (hlifts j i), hblocks]
  rfl

/-- Literal SL lifts discharge the projective block premise. This is the common
consumer for the existing correction-lift task and Hermitian binary coordinates. -/
public theorem correction_blocks_of_sl_lifts
    (e : Models.HermitianSpace ≃ₗ[ZMod 2] (Fin 9 → ZMod 2))
    (B : Matrix.SpecialLinearGroup (Fin 3) M23Geometry.PairPlaneCoordinates.Four →
      Matrix (Fin 9) (Fin 9) (ZMod 2))
    (hB : ∀ A v, e (HermitianTensorThree.binaryAction 1
      (Matrix.SpecialLinearGroup.map M23Geometry.PairPlaneCoordinates.fieldEquiv.toRingHom A) v) =
        (B A).mulVec (e v))
    (lifts : Fin 2 → Fin 22 → M23Geometry.pointwisePairStabilizer)
    (A : Fin 2 → Fin 22 →
      Matrix.SpecialLinearGroup (Fin 3) M23Geometry.PairPlaneCoordinates.Four)
    (hlifts : ∀ j i, pairEmbedding (lifts j i) = explicitMarking *
      MathieuCode.m22Embedding (SixteenSubmodule.GeneratorMatrices.generatorCorrection j i).val *
        explicitMarking⁻¹)
    (hA : ∀ j i, M23Geometry.PairPlane.pointwiseEquiv (lifts j i) =
      QuotientGroup.mk (Matrix.SpecialLinearGroup.map
        M23Geometry.PairPlaneCoordinates.fieldEquiv.toRingHom (A j i)))
    (j : Fin 2) (i : Fin 22) (v : Models.HermitianSpace) :
    nativeCoordinates e
      (Models.pointAction false (SixteenSubmodule.GeneratorMatrices.generatorCorrection j i) v) =
      (B (A j i)).mulVec (nativeCoordinates e v) := by
  apply correction_blocks_of_pair_lifts e lifts (fun j i => B (A j i)) hlifts
  intro j i v
  rw [hA, Models.hermitian_mk]
  exact hB (A j i) v

end Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.NativeComparison
