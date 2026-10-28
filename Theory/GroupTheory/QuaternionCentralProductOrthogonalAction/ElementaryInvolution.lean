module
public import Theory.GroupTheory.QuaternionSplitBlockInvolutions.ActionDichotomy.FixedPlane
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.ElementaryStabilizerSign
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.WreathOuter
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.FactorSign
import all Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.Plane

/-!
# Involutions preserving an elementary eight in a quaternion central product

The factor-sign character is trivial on an elementary-eight stabilizer.
A kernel-checked table on the 72 wreath actors and 16 vectors shows that a
nonidentity involution in this kernel fixes four vectors. Transporting through
the intrinsic square coordinates gives the c₂-or-factor-interchange alternative
on the original quaternion central product.

The Chapter 14 consumer applies this to its actual Sylow involution and seed,
without a marked-cubic or action-type assumption. Source: Aschbacher–Smith,
14.4.4(2),(6), printed p.1007; the square-form convention is Definition E.2.6.
-/

public section

namespace BinaryFourPlus
private instance : DecidableEq Wreath :=
  (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) C2).injective.decidableEq
private instance : Fintype Wreath :=
  Fintype.ofEquiv _ (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) C2).symm
private def eval (w : Wreath) (v : V) : V :=
  if w.right = 1 then
    (planeLinear (w.left 1) v.1, planeLinear (w.left swapIndex) v.2)
  else (planeLinear (w.left 1) v.2, planeLinear (w.left swapIndex) v.1)
private theorem involution_table : ∀ w : Wreath,
    factorSign w = 1 → w ^ 2 = 1 → w ≠ 1 →
      Fintype.card {v : V // eval w v = v} = 4 := by
  decide +kernel

theorem sign_involution_fixed_card (w : Wreath)
    (hs : factorSign w = 1) (h2 : w ^ 2 = 1) (hne : w ≠ 1) :
    Nat.card {v : V // (wreathToIsometry w).val v = v} = 4 := by
  have he (v : V) : eval w v = (wreathToIsometry w).val v :=
    (wreathToIsometry_apply w v).symm
  simpa only [Nat.card_eq_fintype_card, he] using involution_table w hs h2 hne
end BinaryFourPlus

namespace Subgroup.QuaternionCentralProductData
variable {Q : Type*} [Group Q] [Finite Q] (d : QuaternionCentralProductData Q)

theorem elementary_eight_involution_dichotomy
    (E : Subgroup Q) [IsElementaryAbelian 2 E] (hE : Nat.card E = 8)
    (a : MulAut Q) (ha : a ^ 2 = 1)
    (haE : ∀ x ∈ E, a x ∈ E) (hne : quotientAut (center Q) a ≠ 1) :
    d.IsC2 a ∨ d.left.map a.toMonoidHom = d.right := by
  let w := d.quotientWreathAction a
  have hs : BinaryFourPlus.factorSign w = 1 :=
    d.quotientWreathAction_factorSign_one_of_elementary_eight E hE a haE
  have h2 : w ^ 2 = 1 := by dsimp [w]; rw [← map_pow, ha, map_one]
  have hn : w ≠ 1 := by
    intro h
    apply hne
    have hk : a ∈ d.quotientWreathAction.ker := h
    rw [d.quotientWreathAction_ker] at hk
    exact (d.quotientAut_eq_one_iff_inner a).mpr hk
  let e : d.fixedSquareQuotient a ≃
      {v : BinaryFourPlus.V // (BinaryFourPlus.wreathToIsometry w).val v = v} := {
    toFun := fun x => ⟨d.squareCoordinates (Additive.ofMul x.val), by
      rw [← d.squareCoordinates_quotientAut a x.val]
      exact congrArg (fun t => d.squareCoordinates (Additive.ofMul t)) x.property⟩
    invFun := fun x => ⟨(d.squareCoordinates.symm x.val).toMul, by
      change quotientAut (center Q) a (d.squareCoordinates.symm x.val).toMul =
        (d.squareCoordinates.symm x.val).toMul
      apply Additive.ofMul.injective
      apply d.squareCoordinates.injective
      rw [d.squareCoordinates_quotientAut]
      change (BinaryFourPlus.wreathToIsometry w).val
        (d.squareCoordinates (d.squareCoordinates.symm x.val)) =
          d.squareCoordinates (d.squareCoordinates.symm x.val)
      rw [d.squareCoordinates.apply_symm_apply]
      exact x.property⟩
    left_inv := by intro x; apply Subtype.ext; simp
    right_inv := by intro x; apply Subtype.ext; simp }
  have hc : Nat.card (d.fixedSquareQuotient a) = 4 :=
    (Nat.card_congr e).trans (BinaryFourPlus.sign_involution_fixed_card w hs h2 hn)
  rcases d.action_dichotomy_of_fixed_four a ha hc with h | h
  · exact Or.inl ((d.isC2Action_iff_isC2 a).mp h.1)
  · exact Or.inr h.1
end Subgroup.QuaternionCentralProductData
