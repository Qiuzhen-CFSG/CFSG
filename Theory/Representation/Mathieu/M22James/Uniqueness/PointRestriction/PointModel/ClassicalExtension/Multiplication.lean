module

public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel.ReferenceData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
/-!
# Multiplication of the classical point-stabilizer operators

Complementary-pair products satisfy a quadratic multiplication identity with
an adjugate block. Applied to inverse matrices this gives the divided-square
cocycle; transposing and applying Frobenius gives the symmetric-square cocycle.
Their sum proves multiplicativity of exactly `Reference.operator`.

Source context: James (1973), Lemma 8.3, and Aschbacher–Smith H.12.1,
printed pp.393–394. This is explicit matrix algebra, without enumeration of SL₃(4).
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
namespace Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel.Reference
open Matrix
/-- The complementary-pair product law in characteristic two. -/
lemma crossProducts_mul (a b : Matrix (Fin 3) (Fin 3) F) :
    crossProducts (a * b) = adjugate b * crossProducts a +
      crossProducts b * (a.transpose.map (fun x => x ^ 2)) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [crossProducts, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_three, Matrix.adjugate_fin_three,
      CharTwo.sub_eq_add, CharTwo.neg_eq] <;> ring

private abbrev sqMatrix : Matrix (Fin 3) (Fin 3) F →+* Matrix (Fin 3) (Fin 3) F :=
  Representation.SL2FourNatural.fieldFrobenius.toRingHom.mapMatrix

private lemma sqMatrix_sq (a : Matrix (Fin 3) (Fin 3) F) : sqMatrix (sqMatrix a) = a := by
  funext i j
  exact Representation.SL2FourNatural.fieldFrobenius_involutive _

/-- The off-diagonal block is a cocycle for the natural and twisted dual actions. -/
lemma coupling_mul (g h : SL) :
    coupling (g * h) = g.val * coupling h +
      coupling g * ((h⁻¹).val.transpose.map (fun x => x ^ 2)) := by
  have h₁ : crossProducts ((g * h)⁻¹).val =
      g.val * crossProducts h⁻¹.val +
        crossProducts g⁻¹.val * sqMatrix (h⁻¹.val.transpose) := by
    rw [_root_.mul_inv_rev]
    change crossProducts (h⁻¹.val * g⁻¹.val) = _
    rw [crossProducts_mul]
    have hi : adjugate g⁻¹.val = g.val := congrArg Subtype.val (inv_inv g)
    rw [hi]
    rfl
  have h₂ : sqMatrix ((crossProducts (g * h).val).transpose) =
      sqMatrix ((crossProducts g.val).transpose) * sqMatrix (h⁻¹.val.transpose) +
        g.val * sqMatrix ((crossProducts h.val).transpose) := by
    change sqMatrix ((crossProducts (g.val * h.val)).transpose) = _
    rw [crossProducts_mul, Matrix.transpose_add,
      Matrix.transpose_mul, Matrix.transpose_mul]
    change sqMatrix ((crossProducts g.val).transpose * (adjugate h.val).transpose +
      (sqMatrix g.val) * (crossProducts h.val).transpose) = _
    rw [map_add, map_mul, map_mul, sqMatrix_sq]
    rfl
  change crossProducts ((g * h)⁻¹).val + sqMatrix ((crossProducts (g * h).val).transpose) =
    g.val * (crossProducts h⁻¹.val + sqMatrix ((crossProducts h.val).transpose)) +
      (crossProducts g⁻¹.val + sqMatrix ((crossProducts g.val).transpose)) *
        sqMatrix (h⁻¹.val.transpose)
  rw [h₁, h₂, mul_add, add_mul]
  abel

/-- The published six-dimensional operators multiply as the group elements do. -/
lemma operator_mul (g h : SL) : operator (g * h) = operator g * operator h := by
  apply LinearMap.ext
  intro v
  change operator (g * h) v = operator g (operator h v)
  simp only [operator_apply]
  apply Prod.ext
  · change (g.val * h.val) *ᵥ v.1 + coupling (g * h) *ᵥ v.2 =
      g.val *ᵥ (h.val *ᵥ v.1 + coupling h *ᵥ v.2) +
        coupling g *ᵥ (((h⁻¹).val.transpose.map (fun x => x ^ 2)) *ᵥ v.2)
    rw [coupling_mul, Matrix.add_mulVec,
      Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec]
    abel
  · exact LinearMap.congr_fun (quotientRepresentation.map_mul g h) v.2

lemma quotientRepresentation_apply (g : SL) (v : W) : quotientRepresentation g v =
    ((g⁻¹).val.transpose.map (fun x => x ^ 2)) *ᵥ v := rfl

/-- The classical six-dimensional field extension with the specified operators. -/
def representation : Representation F SL V where
  toFun := operator
  map_one' := operator_one
  map_mul' := operator_mul

/-- Restriction of the same operators to the binary prime field. -/
def binaryRepresentation : Representation (ZMod 2) SL V where
  toFun g := (representation g).restrictScalars (ZMod 2)
  map_one' := by
    apply LinearMap.ext
    intro v
    exact LinearMap.congr_fun representation.map_one v
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    exact LinearMap.congr_fun (representation.map_mul g h) v
end Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel.Reference
