module
public import Theory.Representation.SL3FourNaturalDual

/-!
# Coordinates for the classical extension used in the point comparison

For a three-by-three matrix a, P(a) records products in complementary column
pairs. The proposed six-dimensional field operator has blocks
(g, P(g⁻¹) + Frobenius(P(g)ᵀ); 0, Frobenius(g⁻ᵀ)). The two summands in the
upper-right block come from the divided square of the dual natural module
and the symmetric square of the Frobenius natural module, respectively.

This file defines the operators and checks their invariant block, quotient,
identity and central scalar. It does not assert multiplicativity or the
comparison with the Mathieu matrices. Those require additional proofs.
The coordinate convention fixes the central scalar as omega I.

Source context: James (1973), Lemma 8.3, as used in Aschbacher–Smith H.12.1,
printed pp.393–394, where the binary restriction is described as an extension
of a natural module by its dual. The formulas here are explicit matrix algebra;
no character-table or ATLAS representation assertion is used as a theorem.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel.Reference
open Matrix
abbrev F := Representation.SL2FourNatural.F
abbrev W := Fin 3 → F
abbrev V := W × W
abbrev SL := Representation.SL3FourNaturalDual.SL

/-- Products in the complementary column pair (12), (02), (01). -/
def crossProducts (a : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 3) (Fin 3) F :=
  fun i j => a j (![1, 0, 0] i) * a j (![2, 2, 1] i)

/-- The sum of the off-diagonal blocks from the two classical quadratic extensions. -/
def coupling (g : SL) : Matrix (Fin 3) (Fin 3) F :=
  crossProducts g⁻¹.val + ((crossProducts g.val).transpose.map (fun x => x ^ 2))

/-- The Frobenius twist of the inverse-transpose natural action. -/
def quotientRepresentation : Representation F SL W :=
  (Representation.specialLinearNatural 3).comp
    ((SpecialLinearGroup.map Representation.SL2FourNatural.fieldFrobenius.toRingHom).comp
      SpecialLinearGroup.inverseTranspose)

/-- An explicit linear operator on all six field coordinates.
Multiplicativity and comparison with the Mathieu matrices are separate obligations. -/
def operator (g : SL) : Module.End F V :=
  LinearMap.prod
    (((Representation.specialLinearNatural 3) g).comp (LinearMap.fst F W W) +
      (coupling g).mulVecLin.comp (LinearMap.snd F W W))
    ((quotientRepresentation g).comp (LinearMap.snd F W W))

lemma operator_apply (g : SL) (v : V) :
    operator g v = (g.val *ᵥ v.1 + coupling g *ᵥ v.2,
      ((g⁻¹).val.transpose.map (fun x => x ^ 2)) *ᵥ v.2) := rfl

lemma operator_inclusion (g : SL) (v : W) : operator g (v,0) = (g.val *ᵥ v,0) := by
  rw [operator_apply, Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]

lemma operator_quotient (g : SL) (v : V) : (operator g v).2 = quotientRepresentation g v.2 := rfl

lemma coupling_one : coupling 1 = 0 := by
  simp only [coupling, inv_one]
  decide +kernel

lemma operator_one : operator 1 = 1 := by
  apply LinearMap.ext
  intro v
  change ((Representation.specialLinearNatural 3) 1 v.1 + coupling 1 *ᵥ v.2,
    quotientRepresentation 1 v.2) = v
  rw [map_one, map_one, coupling_one, Matrix.zero_mulVec, add_zero]
  rfl

/-- The scalar matrix specified by the actual central-field coordinates. -/
def scalar : SL := ⟨Matrix.diagonal (fun _ => (QuadraticAlgebra.omega : F)), by
  rw [Matrix.det_diagonal]
  decide +kernel⟩

lemma coupling_scalar : coupling scalar = 0 := by decide +kernel

lemma quotient_scalar : ((scalar⁻¹).val.transpose.map (fun x => x ^ 2)) =
    Matrix.diagonal (fun _ => (QuadraticAlgebra.omega : F)) := by decide +kernel

lemma operator_scalar (v : V) : operator scalar v = (QuadraticAlgebra.omega : F) • v := by
  rw [operator_apply, coupling_scalar, Matrix.zero_mulVec, add_zero, quotient_scalar]
  apply Prod.ext <;> funext i <;>
    simp [scalar, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]

lemma finrank_binary : Module.finrank (ZMod 2) V = 12 :=
  Representation.SL3FourNaturalDual.finrank_space

end Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel.Reference
