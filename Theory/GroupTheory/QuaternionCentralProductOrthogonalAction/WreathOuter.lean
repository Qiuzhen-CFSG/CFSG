module
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.Geometry
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.Kernel
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Mathlib.GroupTheory.Nilpotent
/-!
# The actual outer wreath action of a quaternion central product

The square action of an intrinsic Q₈*Q₈ has inner automorphisms as kernel.
It therefore embeds the literal outer group in the orthogonal wreath model
S₃ wr C₂. This model is solvable, and the inner two-group gives solvability
of the full automorphism group. The original wreath-centralizer consumer
uses this after proving normality of its marked extraspecial subgroup.

Source: Aschbacher–Smith 13.9.8, printed p.972; the intrinsic square action
is the geometry of 14.2.21, printed p.988.
-/
public section
open Subgroup
namespace BinaryFourPlus

theorem wreath_isSolvable : Group.IsSolvable Wreath := by
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
    Group.isSolvable_of_isSolvable_injective
      (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))
  let f : Wreath →* C2 := RegularWreathProduct.rightHom
  let c : C2 := Multiplicative.ofAdd 1
  have hcoord : ∀ i : C2, i = 1 ∨ i = c := by decide
  let j : f.ker →* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) := {
    toFun := fun x => (x.val.left 1,x.val.left c)
    map_one' := rfl
    map_mul' := fun x y => by
      have hx : x.val.right = 1 := x.property
      ext <;> simp [RegularWreathProduct.mul_left,hx] }
  have hj : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    apply RegularWreathProduct.ext
    · funext i
      rcases hcoord i with rfl | rfl
      · exact congrArg Prod.fst hxy
      · exact congrArg Prod.snd hxy
    · exact x.property.trans y.property.symm
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective hj
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by rw [range_subtype])

end BinaryFourPlus
namespace Subgroup.QuaternionCentralProductData
variable {Q : Type*} [Group Q] [Finite Q] (d : QuaternionCentralProductData Q)

theorem quotientWreathAction_ker : d.quotientWreathAction.ker = MulAut.innerSubgroup Q := by
  ext a
  change d.quotientWreathAction a = 1 ↔ a ∈ (MulAut.conj : Q →* MulAut Q).range
  rw [← d.quotientAut_eq_one_iff_inner]
  constructor
  · intro ha
    have hh : d.squareIsometryAction a = 1 :=
      d.squareIsometriesEquivWreath.injective (by rw [← d.quotientWreathAction_eq,map_one]; exact ha)
    apply MulEquiv.ext
    intro v
    have hv := congrArg (fun b : d.squareIsometries => b.val (Additive.ofMul v)) hh
    rw [d.squareIsometryAction_apply] at hv
    exact congrArg Additive.toMul hv
  · intro ha
    have hh : d.squareIsometryAction a = 1 := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro v
      rw [show v = Additive.ofMul v.toMul from rfl, d.squareIsometryAction_apply,ha]
      rfl
    rw [d.quotientWreathAction_eq,hh,map_one]

noncomputable def outerWreathEmbedding : MulAut.Outer Q →* BinaryFourPlus.Wreath :=
  (d.quotientWreathAction.range).subtype.comp
    (((QuotientGroup.quotientMulEquivOfEq d.quotientWreathAction_ker.symm).trans
      (QuotientGroup.quotientKerEquivRange d.quotientWreathAction)).toMonoidHom)

theorem outerWreathEmbedding_mk (a : MulAut Q) :
    d.outerWreathEmbedding (QuotientGroup.mk' (MulAut.innerSubgroup Q) a) =
      d.quotientWreathAction a := by rfl

theorem outerWreathEmbedding_injective : Function.Injective d.outerWreathEmbedding :=
  Subtype.val_injective.comp
    (((QuotientGroup.quotientMulEquivOfEq d.quotientWreathAction_ker.symm).trans
      (QuotientGroup.quotientKerEquivRange d.quotientWreathAction)).injective)

include d in
theorem mulAut_isSolvable : Group.IsSolvable (MulAut Q) := by
  let : Group.IsSolvable BinaryFourPlus.Wreath := BinaryFourPlus.wreath_isSolvable
  have hp : IsPGroup 2 Q := IsPGroup.of_card (n := 5) (by rw [d.card]; norm_num)
  let : Group.IsNilpotent Q := hp.isNilpotent
  apply Group.isSolvable_of_ker_le_range (MulAut.conj : Q →* MulAut Q)
    d.quotientWreathAction
  exact d.quotientWreathAction_ker.le

end Subgroup.QuaternionCentralProductData
