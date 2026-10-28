module
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.Geometry
public import Theory.GroupTheory.QuaternionCentralProductFactorNormality
import all Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.Geometry.Coordinates
/-!
# The intrinsic factor marking in the square-wreath action

The first and second square-coordinate planes come from the two original
quaternion factors. Polar commutation makes the opposite coordinates zero.
Applying the actual wreath action to a marked quaternion generator shows
that its swapping coordinate is trivial exactly when the original left
factor is preserved.

The internal import of Coordinates is intentional: this descendant proves
public behavior lemmas for the existing unexposed coordinate definitions,
without changing their foundational API or exposing their implementation.
Source: Aschbacher–Smith 13.9.8, printed p.972.
-/
public section
open Subgroup
open scoped commutatorElement
namespace Subgroup.QuaternionCentralProductData
variable {Q : Type*} [Group Q] [Finite Q] (d : QuaternionCentralProductData Q)

/-- The selected square coordinates keep the original factor generators. -/
theorem squareCoordinates_factor_left (i : Fin 2) :
    d.squareCoordinates (d.factorVector d.left d.left_model.some i) =
      (Pi.single i 1,0) := d.coordinates_left _ _ i

theorem squareCoordinates_factor_right (i : Fin 2) :
    d.squareCoordinates (d.factorVector d.right d.right_model.some i) =
      (0,Pi.single i 1) := d.coordinates_right _ _ i

theorem squareCoordinates_mk_left_zero (x : Q) (hx : x ∈ d.left) :
    (d.squareCoordinates (Additive.ofMul (QuotientGroup.mk' (center Q) x))).2 = 0 := by
  change (![d.quadraticForm.polarBilin (Additive.ofMul (QuotientGroup.mk' (center Q) x))
    (d.factorVector d.right d.right_model.some 1),
    d.quadraticForm.polarBilin (Additive.ofMul (QuotientGroup.mk' (center Q) x))
    (d.factorVector d.right d.right_model.some 0)] : Fin 2 → ZMod 2) = 0
  funext i
  fin_cases i <;> dsimp only
  all_goals
    change d.quadraticForm.polarBilin _ (d.factorVector _ _ _) = 0
    rw [factorVector,d.polarBilin_mk,d.centerCoordinate_eq_zero_iff]
    apply Subtype.ext
    exact commutatorElement_eq_one_iff_mul_comm.mpr (d.commute x hx _ (Subtype.property _))

theorem squareCoordinates_mk_right_zero (x : Q) (hx : x ∈ d.right) :
    (d.squareCoordinates (Additive.ofMul (QuotientGroup.mk' (center Q) x))).1 = 0 := by
  change (![d.quadraticForm.polarBilin (Additive.ofMul (QuotientGroup.mk' (center Q) x))
    (d.factorVector d.left d.left_model.some 1),
    d.quadraticForm.polarBilin (Additive.ofMul (QuotientGroup.mk' (center Q) x))
    (d.factorVector d.left d.left_model.some 0)] : Fin 2 → ZMod 2) = 0
  funext i
  fin_cases i <;> dsimp only
  all_goals
    change d.quadraticForm.polarBilin _ (d.factorVector _ _ _) = 0
    rw [factorVector,d.polarBilin_mk,d.centerCoordinate_eq_zero_iff]
    apply Subtype.ext
    exact commutatorElement_eq_one_iff_mul_comm.mpr (d.commute _ (Subtype.property _) x hx).symm


/-- The wreath swapping coordinate detects preservation of the actual left
quaternion factor, independently of the selected quaternion generators. -/
theorem quotientWreathAction_right_eq_one_iff (a : MulAut Q) :
    (d.quotientWreathAction a).right = 1 ↔ d.left.map a.toMonoidHom = d.left := by
  let x : Q := (d.left_model.some.symm (QuaternionGroup.a 1) : d.left)
  let v := Additive.ofMul (QuotientGroup.mk' (center Q) x)
  have hx : x ∈ d.left := Subtype.property _
  have hv : d.squareCoordinates v = (Pi.single (0 : Fin 2) 1,0) :=
    d.squareCoordinates_factor_left 0
  have hb : (Pi.single (0 : Fin 2) (1 : ZMod 2) : Fin 2 → ZMod 2) ≠ 0 := by decide
  have hpoint (i : BinaryFourPlus.C2) :=
    d.quotientWreathAction_apply a (QuotientGroup.mk' (center Q) x) i
  constructor
  · intro hw
    rcases (d.quaternion_subgroup_iff (d.left.map a.toMonoidHom)).mp
      ⟨(a.subgroupMap d.left).symm.trans d.left_model.some⟩ with hl | hr
    · exact hl
    exfalso
    have hax : a x ∈ d.right := hr ▸ mem_map_of_mem a.toMonoidHom hx
    have hzero := d.squareCoordinates_mk_right_zero (a x) hax
    have he := hpoint 1
    rw [quotientAut_apply_mk] at he
    simp only [hw,inv_one,one_mul,BinaryFourPlus.coordinate,ite_true,hzero] at he
    change 0 = BinaryFourPlus.planeLinear ((d.quotientWreathAction a).left 1)
      (d.squareCoordinates v).1 at he
    rw [hv] at he
    exact hb ((BinaryFourPlus.planeLinear _).injective (he.symm.trans (map_zero _).symm))
  · intro hl
    by_contra hw
    have htwo : ∀ i : BinaryFourPlus.C2, i = 1 ∨ i = BinaryFourPlus.swapIndex := by decide
    have hw' := (htwo (d.quotientWreathAction a).right).resolve_left hw
    have hax : a x ∈ d.left := hl ▸ mem_map_of_mem a.toMonoidHom hx
    have hzero := d.squareCoordinates_mk_left_zero (a x) hax
    have he := hpoint BinaryFourPlus.swapIndex
    rw [quotientAut_apply_mk] at he
    simp only [hw',BinaryFourPlus.swapIndex_inv,BinaryFourPlus.swapIndex_mul_self,
      BinaryFourPlus.coordinate,BinaryFourPlus.swapIndex_ne_one,ite_false,ite_true,hzero] at he
    change 0 = BinaryFourPlus.planeLinear ((d.quotientWreathAction a).left BinaryFourPlus.swapIndex)
      (d.squareCoordinates v).1 at he
    rw [hv] at he
    exact hb ((BinaryFourPlus.planeLinear _).injective (he.symm.trans (map_zero _).symm))

end Subgroup.QuaternionCentralProductData
