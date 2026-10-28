module
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.FanoDecomposition.Basic
public import Theory.SpecificGroups.PSL3Two.Parabolics.CompatibleMarking

/-!
# Duality of the Fano cores preserving a marked flag

Coordinate duality intertwines inverse transpose. Compose it with the
representation of the reversing matrix to obtain the flag-preserving
outer automorphism. The resulting equivalence swaps the marked point and
line parabolics while retaining their common Sylow subgroup. Restriction
keeps the literal actor map. This transports the two socle rows in
Aschbacher–Smith 13.4.14, printed p.911, using H.5, pp.385–386.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Representation Matrix.PSL3Two
namespace BinaryLinearThree.FanoDecomposition

private theorem flagDuality_apply (g : Group) :
    flagDuality g = (Bruhat.perm 5) * AutomorphismAction.graph g * (Bruhat.perm 5)⁻¹ := by
  change (Bruhat.perm 5) * g.transpose⁻¹ * (Bruhat.perm 5)⁻¹ =
    (Bruhat.perm 5) * g⁻¹.transpose * (Bruhat.perm 5)⁻¹
  have ht : g⁻¹.transpose = g.transpose⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    apply Subtype.ext
    change g⁻¹.val.transpose * g.val.transpose = (1 : Matrix (Fin 3) (Fin 3) (ZMod 2))
    rw [←Matrix.transpose_mul,←Matrix.SpecialLinearGroup.coe_mul,mul_inv_cancel]
    exact Matrix.transpose_one
  rw [ht]

/-- The coordinate reversal makes core duality preserve the marked Sylow
and exchange the two marked parabolics. -/
def flagCoreDualityEquiv : Representation.Equiv
    (U₂.comp flagDuality.toMonoidHom) lineCoreRepresentation := by
  let e : Representation.Equiv (U₂.comp flagDuality.toMonoidHom)
      (U₂.comp AutomorphismAction.graph.toMonoidHom) := {
    toLinearEquiv := LinearMap.GeneralLinearGroup.toLinearEquiv
      (U₂.asGroupHom (Bruhat.perm 5)⁻¹)
    isIntertwining' g := by
      change U₂ (Bruhat.perm 5)⁻¹ * U₂ (flagDuality g) =
        U₂ (AutomorphismAction.graph g) * U₂ (Bruhat.perm 5)⁻¹
      rw [←U₂.map_mul,←U₂.map_mul,flagDuality_apply]
      exact congrArg U₂ (by group) }
  exact e.trans coreDualityEquiv
/-- Restrict flag-preserving core duality along the original actor map. -/
def flagCoreDuality_comp {H : Type*} [_root_.Group H] (f : H →* Group) :
    Representation.Equiv (U₂.comp (flagDuality.toMonoidHom.comp f))
      (lineCoreRepresentation.comp f) where
  toLinearEquiv := flagCoreDualityEquiv.toLinearEquiv
  isIntertwining' h := flagCoreDualityEquiv.isIntertwining' (f h)
end BinaryLinearThree.FanoDecomposition
