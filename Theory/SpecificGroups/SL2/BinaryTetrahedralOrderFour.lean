module
public import Theory.SpecificGroups.SL2.BinaryTetrahedral
public import Mathlib.Tactic
/-!
# The order-four class of SL2(3)

The six elements of order four form one conjugacy class. A checked table in
Q8 ⋊ C3 is transported through the explicit binary tetrahedral matrix map.
This supplies the actual quaternion-factor conjugations on printed p.546
of Aschbacher--Smith 2.4.29.
-/
public section
namespace GLS3.Chapter5.SchurPresentation
private abbrev BT := QuaternionGroup 2 ⋊[q8C3Action] Multiplicative (ZMod 3)
private instance : DecidableEq BT := SemidirectProduct.equivProd.injective.decidableEq
private instance : Fintype BT := Fintype.ofEquiv _ SemidirectProduct.equivProd.symm
private theorem order_four_conjugacy_table :
    ∀ x y : BT, x^2 ≠ 1 → x^4=1 → y^2 ≠ 1 → y^4=1 →
      ∃ g : BT, g*x*g⁻¹=y := by decide +kernel

/-- The six elements of order four in the binary tetrahedral group form one conjugacy class. -/
theorem sl23_order_four_isConj (x y : SL23) (hx : orderOf x=4) (hy : orderOf y=4) : IsConj x y := by
  let e := binaryTetrahedralEquivSL
  have hpow (a : SL23) (ha : orderOf a=4) : (e.symm a)^2≠1 ∧ (e.symm a)^4=1 := by
    constructor
    · intro hh
      have hdiv : orderOf (e.symm a) ∣ 2 := orderOf_dvd_of_pow_eq_one hh
      rw [e.symm.orderOf_eq,ha] at hdiv
      norm_num at hdiv
    · rw [← map_pow,←ha,pow_orderOf_eq_one,map_one]
  have hxx := hpow x hx
  have hyy := hpow y hy
  obtain ⟨g,hg⟩ := order_four_conjugacy_table (e.symm x) (e.symm y) hxx.1 hxx.2 hyy.1 hyy.2
  apply isConj_iff.mpr
  refine ⟨e g,?_⟩
  simpa only [map_mul,map_inv,e.apply_symm_apply] using congrArg e hg
end GLS3.Chapter5.SchurPresentation
