module

public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.TreeSylow
public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# The binary-tree Sylow as a dihedral wreath product

The actual binary-tree subgroup of S₈ has order 128, so it is Sylow.
Mathlib's Sylow wreath theorem identifies it with three iterated copies of C₂.
The first two copies form D₈: an explicit rotation and reflection give an
injective homomorphism from DihedralGroup 4, and both groups have order eight.
Thus the tree subgroup is the actual regular wreath product D₈ wreath C₂.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, completion of
the proof of Theorem 16.3.7, printed p.1182 / PDF p.1199. The iterated-wreath
construction is Mathlib's Sylow.mulEquivIteratedWreathProduct.
-/

public section
namespace Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
open Subgroup

private abbrev CTwo := Multiplicative (ZMod 2)
private abbrev D8 := DihedralGroup 4
private abbrev W8 := RegularWreathProduct D8 CTwo

private instance instDecEqW2 : DecidableEq (RegularWreathProduct CTwo CTwo) :=
  fun a b => decidable_of_iff (a.left = b.left ∧ a.right = b.right)
    RegularWreathProduct.ext_iff.symm
private instance instFintypeW2 : Fintype (RegularWreathProduct CTwo CTwo) :=
  Fintype.ofEquiv ((CTwo → CTwo) × CTwo)
    (RegularWreathProduct.equivProd CTwo CTwo).symm
private def wreathRot : RegularWreathProduct CTwo CTwo :=
  let c : CTwo := Multiplicative.ofAdd 1
  let a : RegularWreathProduct CTwo CTwo := ⟨fun q => if q = c then c else 1, 1⟩
  let b : RegularWreathProduct CTwo CTwo := ⟨1, c⟩
  a * b
private def wreathRefl : RegularWreathProduct CTwo CTwo :=
  let c : CTwo := Multiplicative.ofAdd 1
  ⟨1, c⟩
private def wreathDihHom : D8 →* RegularWreathProduct CTwo CTwo :=
  let modelMap : D8 → RegularWreathProduct CTwo CTwo := fun x => match x with
    | .r exponent => wreathRot ^ exponent.val
    | .sr exponent => wreathRefl * wreathRot ^ exponent.val
  { toFun := modelMap
    map_one' := by set_option maxRecDepth 10000 in decide +kernel
    map_mul' := by set_option maxRecDepth 10000 in decide +kernel }
private theorem wreathDihHom_inj : Function.Injective wreathDihHom := by
  set_option maxRecDepth 10000 in set_option maxHeartbeats 1000000 in decide +kernel
private noncomputable def c2_dih : (RegularWreathProduct CTwo CTwo) ≃* D8 := by
  let hcard : Fintype.card (RegularWreathProduct CTwo CTwo) = Fintype.card D8 := by
    rw [← Nat.card_eq_fintype_card, RegularWreathProduct.card]
    rw [← Nat.card_eq_fintype_card, DihedralGroup.nat_card]
    norm_num [Nat.card_eq_fintype_card, CTwo]
  exact (MulEquiv.ofBijective wreathDihHom
    ((Fintype.bijective_iff_injective_and_card wreathDihHom).mpr
      ⟨wreathDihHom_inj, hcard.symm⟩)).symm
private noncomputable def unit_wreath :
    RegularWreathProduct PUnit CTwo ≃* CTwo := {
  toFun := fun x => x.right
  invFun := fun q => ⟨fun _ => 1, q⟩
  left_inv := by intro x; apply RegularWreathProduct.ext <;> simp
  right_inv := by intro x; simp
  map_mul' := by intro x y; simp [RegularWreathProduct.mul_right] }
private noncomputable def iter_wreath : IteratedWreathProduct CTwo 3 ≃* W8 := by
  let e1 : IteratedWreathProduct CTwo 1 ≃* CTwo := by
    change RegularWreathProduct PUnit CTwo ≃* CTwo
    exact unit_wreath
  let e2 : IteratedWreathProduct CTwo 2 ≃*
      RegularWreathProduct CTwo CTwo := by
    change RegularWreathProduct (IteratedWreathProduct CTwo 1) CTwo ≃* _
    exact RegularWreathProduct.congr e1 (MulEquiv.refl CTwo)
  let e3 : IteratedWreathProduct CTwo 3 ≃* W8 := by
    change RegularWreathProduct (IteratedWreathProduct CTwo 2) CTwo ≃* _
    exact (RegularWreathProduct.congr e2 (MulEquiv.refl CTwo)).trans
      (RegularWreathProduct.congr c2_dih (MulEquiv.refl CTwo))
  exact e3

/-- The actual binary-tree subgroup, as a Sylow two-subgroup of S₈. -/
@[expose] noncomputable def treeSylow : Sylow 2 (Equiv.Perm (Fin 8)) :=
  Sylow.ofCard treeGroup (by
    rw [card_treeGroup, card_s8]
    rw [show 40320 = 2 ^ 7 * 315 by rfl, Nat.factorization_mul (by decide) (by decide),
      Nat.factorization_pow]
    norm_num [Nat.prime_two.factorization,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 315)])

/-- The binary-tree subgroup is the actual dihedral regular wreath product. -/
noncomputable def treeWreathEquiv : treeGroup ≃*
    RegularWreathProduct (DihedralGroup 4) (Multiplicative (ZMod 2)) := by
  let e := Sylow.mulEquivIteratedWreathProduct 2 3 (Fin 8)
    (by norm_num [Nat.card_eq_fintype_card, CTwo]) CTwo
    (by norm_num [Nat.card_eq_fintype_card, CTwo]) treeSylow
  exact e.trans iter_wreath

@[simp] theorem treeSylow_coe : (treeSylow : Subgroup S8) = treeGroup := rfl

end Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
