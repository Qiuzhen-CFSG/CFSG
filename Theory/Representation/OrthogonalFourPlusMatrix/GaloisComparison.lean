module
public import Theory.Representation.OrthogonalFourPlusMatrix.Comparison
public import Theory.SpecificGroups.ClassicalOrthogonal.PlusFieldTransport

/-!
# Canonical-field coordinates for the binary determinant tensor

Coefficient transport identifies the elementary orthogonal action over the
canonical field GF(4) with the concrete binary determinant model. The group
map and the binary vector coordinates intertwine the literal actions. This
is the coordinate comparison needed for the tensor row of G.11.2(7).
-/

public noncomputable section
namespace ClassicalOrthogonal.FourPlusMatrix.Binary
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
attribute [local instance 2000] instAlgebraZModGaloisField

/-- The canonical-field elementary group is the concrete pair of SL₂(4)'s. -/
def galoisGroupEquiv : OmegaPlus 2 (GaloisField 2 2) ≃* G :=
  (((PlusFieldTransport.orthogonalEquiv Representation.SL2FourNatural.fieldEquiv.symm 2).subgroupMap _).trans
    (MulEquiv.subgroupCongr (PlusFieldTransport.map_elementary Representation.SL2FourNatural.fieldEquiv.symm 2))).trans
    (FourPlusMatrix.elementaryEquiv (F := F)).symm

private def coefficientCoordinates : VectorD 2 (GaloisField 2 2) ≃ₗ[ZMod 2] VectorD 2 F :=
  { (PlusFieldTransport.coefficientEquiv Representation.SL2FourNatural.fieldEquiv.symm 2).toAddEquiv with
    map_smul' c v :=
      ZMod.map_smul (PlusFieldTransport.coefficientEquiv
        Representation.SL2FourNatural.fieldEquiv.symm 2).toAddEquiv.toAddMonoidHom c v }


/-- Binary coordinates on the original canonical-field orthogonal space. -/
def galoisCoordinates : VectorD 2 (GaloisField 2 2) ≃ₗ[ZMod 2] V :=
  coefficientCoordinates.trans binaryCoordinates

/-- These coordinates identify the elementary action, before projectivization,
with the actual determinant tensor action. -/
theorem galoisCoordinates_intertwines (g : OmegaPlus 2 (GaloisField 2 2))
    (v : VectorD 2 (GaloisField 2 2)) :
    galoisCoordinates (subgroupNatural (OmegaPlus 2 (GaloisField 2 2)) g v) =
      action (galoisGroupEquiv g) (galoisCoordinates v) := by
  let q := (((PlusFieldTransport.orthogonalEquiv Representation.SL2FourNatural.fieldEquiv.symm 2).subgroupMap _).trans
    (MulEquiv.subgroupCongr (PlusFieldTransport.map_elementary Representation.SL2FourNatural.fieldEquiv.symm 2))) g
  have hq : toOrthogonal (galoisGroupEquiv g) = q.val := by
    have he := (FourPlusMatrix.elementaryEquiv (F := F)).apply_symm_apply q
    exact congrArg Subtype.val he
  have hc := PlusFieldTransport.orthogonalEquiv_apply
    Representation.SL2FourNatural.fieldEquiv.symm 2 g.val v
  change q.val.val (coefficientCoordinates v) =
    coefficientCoordinates (subgroupNatural (OmegaPlus 2 (GaloisField 2 2)) g v) at hc
  change binaryCoordinates
    (coefficientCoordinates (subgroupNatural (OmegaPlus 2 (GaloisField 2 2)) g v)) = _
  rw [← hc,← hq]
  exact binaryCoordinates_equivariant (galoisGroupEquiv g) (coefficientCoordinates v)
end ClassicalOrthogonal.FourPlusMatrix.Binary
