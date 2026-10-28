module
public import Theory.Representation.PSL3Two.NaturalDualMarking

/-!
# Matrix coordinates for the same natural and dual sections

The binary SL-to-linear-group equivalence retains the natural action.
The inverse dot-product equivalence converts the original dual coordinates
to the inverse-transpose matrix action. Both sections keep their original
numerators, common kernel and the same actor map.

Source application: Aschbacher--Smith, the index bounds on printed p.1042.
-/

public section
open Subgroup Representation Matrix
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
open Matrix.PSL3Two.MarkedAutomorphisms.AffineConstituents
namespace Matrix.PSL3Two.NaturalDualMarking
variable {G : Type*} [Group G] {L A B Z : Subgroup G}

private theorem matrix_dual_pairing (a : SL) (v w : Space) :
    dotProduct (fullDual a v) w = dotProduct v ((BinaryLinear.OuterCyclic.slEquivLinear 3 a).symm w) := by
  have ht : inverseTranspose a = SpecialLinearGroup.transpose a⁻¹ := by
    apply inv_eq_of_mul_eq_one_left
    apply Subtype.ext
    change a⁻¹.val.transpose * a.val.transpose = 1
    rw [← Matrix.transpose_mul]
    change (a*a⁻¹).val.transpose = 1
    rw [mul_inv_cancel]
    exact Matrix.transpose_one
  change dotProduct ((inverseTranspose a).val.mulVec v) w = _
  rw [ht]
  change dotProduct (a⁻¹.val.transpose.mulVec v) w =
    dotProduct v ((BinaryLinear.OuterCyclic.slEquivLinear 3 a)⁻¹ w)
  rw [←map_inv]
  change dotProduct (a⁻¹.val.transpose.mulVec v) w = dotProduct v (a⁻¹.val.mulVec w)
  rw [Matrix.dotProduct_mulVec,Matrix.mulVec_transpose]

/-- Retain the literal pair and its actor while changing the linear-group
coordinates to matrices and the dual coordinates to dot-product vectors. -/
theorem exists_matrix_pair
    (f : L →* BinaryLinear.GL Space)
    (n : BinaryConjugationSection L A Z (NatRep.comp f))
    (d : BinaryConjugationSection L B Z (Representation.dual (NatRep.comp f))) :
    let q := (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.toMonoidHom.comp f
    Nonempty (BinaryConjugationSection L A Z ((specialLinearNatural 3).comp q)) ∧
      Nonempty (BinaryConjugationSection L B Z (fullDual.comp q)) := by
  dsimp only
  let q := (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.toMonoidHom.comp f
  have hq (x : L) : BinaryLinear.OuterCyclic.slEquivLinear 3 (q x) = f x :=
    (BinaryLinear.OuterCyclic.slEquivLinear 3).apply_symm_apply _
  let n' : BinaryConjugationSection L A Z ((specialLinearNatural 3).comp q) := {
    n with
    equivariant := by
      intro x a
      rw [n.equivariant]
      change f x (n.coordinates a).toAdd =
        BinaryLinear.OuterCyclic.slEquivLinear 3 (q x) (n.coordinates a).toAdd
      rw [hq] }
  let D := (dotProductEquiv (ZMod 2) (Fin 3)).symm
  have hD (v : Module.Dual (ZMod 2) Space) (w : Space) : dotProduct (D v) w = v w :=
    LinearMap.congr_fun ((dotProductEquiv (ZMod 2) (Fin 3)).apply_symm_apply v) w
  let d' : BinaryConjugationSection L B Z (fullDual.comp q) := {
    section_le := d.section_le
    kernel_le := d.kernel_le
    normalized := d.normalized
    coordinates := D.toAddEquiv.toMultiplicative.toMonoidHom.comp d.coordinates
    onto := D.toAddEquiv.toMultiplicative.surjective.comp d.onto
    kernel_eq := by
      ext b
      change D (d.coordinates b).toAdd = 0 ↔ (b:G) ∈ Z
      rw [D.map_eq_zero_iff]
      exact d.coordinates_eq_one_iff b
    equivariant := by
      intro x b
      apply (dotProductEquiv (ZMod 2) (Fin 3)).injective
      apply LinearMap.ext
      intro w
      change dotProduct (D (d.coordinates _).toAdd) w = dotProduct (fullDual (q x) (D (d.coordinates b).toAdd)) w
      rw [hD,d.equivariant,matrix_dual_pairing,hD]
      change (d.coordinates b).toAdd (f x⁻¹ w) = (d.coordinates b).toAdd ((BinaryLinear.OuterCyclic.slEquivLinear 3 (q x))⁻¹ w)
      rw [map_inv,hq] }
  exact ⟨⟨n'⟩,⟨d'⟩⟩
end Matrix.PSL3Two.NaturalDualMarking
