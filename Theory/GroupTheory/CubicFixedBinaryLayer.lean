module
public import Theory.ElementaryAbelian.Basic

/-!
# Cubic automorphisms with fixed binary displacement

If a cubic automorphism fixes a binary layer pointwise, an element moved
only within that layer is fixed. Applying the automorphism twice cancels
the binary displacement; applying it three times is the identity.

This detects the original residual Sylow three-subgroups on both singular
point quotients in Aschbacher--Smith, proof of 12.6.26, pp.831--832.
-/

public section
open Subgroup
namespace Theory.GroupTheory
/-- A cubic automorphism fixing a binary layer cannot move an element only
inside that fixed layer. -/
theorem cubic_fixed_of_binary_displacement {X : Type*} [Group X]
    (a : MulAut X) (ha : a^3=1) (Z : Subgroup X) [IsElementaryAbelian 2 Z]
    (hz : ∀ z ∈ Z, a z=z) (x : X) (hx : a x*x⁻¹ ∈ Z) : a x=x := by
  let d := a x*x⁻¹
  have hd : a d=d := hz d hx
  have hd2 : d*d=1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) d hx
  have hdx : a x=d*x := by simp [d]
  have htwo : a (a x)=x := by
    calc
      a (a x) = a (d*x) := congrArg a hdx
      _ = d*(d*x) := by rw [map_mul,hd,←hdx,hdx]
      _ = x := by rw [←mul_assoc,hd2,one_mul]
  have hthree : a (a (a x))=x := by
    have hh := DFunLike.congr_fun ha x
    simpa only [pow_succ,pow_zero,MulAut.mul_apply,MulAut.one_apply] using hh
  exact (hthree.symm.trans (congrArg a htwo)).symm
end Theory.GroupTheory
