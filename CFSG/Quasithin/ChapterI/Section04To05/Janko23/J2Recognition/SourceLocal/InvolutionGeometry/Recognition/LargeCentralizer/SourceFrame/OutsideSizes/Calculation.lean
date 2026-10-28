module

public import Theory.GroupTheory.MinusExtraspecialA5Fusion.Calculation

/-!
# Fixed-point certificate for the outside involution action

The established five-bit coordinates encode the minus extraspecial core.
The generator relations prune the finite calculation, and the action must
be involutive and move four of the five singular points. Under precisely
these tests, the fixed set has four elements. All computation is checked
by the kernel; no square-root hypothesis is used.

This is the model calculation underlying Aschbacher, *Sporadic Groups*
(1994), 46.8 and 46.11, printed pp.253–255.
-/

namespace J2OutsideSizesCalculation
open MinusExtraspecial.FixedFourCalculation
open MinusExtraspecial.FixedFourCalculation.Outside

def check : Bool := all.all fun u => mul u u == 0 || all.all fun v =>
  mul v v != mul u u || mul v u != mul (inv u) v || all.all fun r =>
  mul r r != 0 || mul r u != mul u r || mul r v != mul v r || all.all fun s =>
  mul s s != 0 || mul s u != mul u s || mul s v != mul v s ||
  mul s r != mul (mul (mul u u) r) s || !Outside.invol u v r s || moved u v r s != 4 ||
  (all.map fun x => if word u v r s x == x then (1 : BitVec 6) else 0).sum == 4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check_eq_true : check = true := by decide +kernel

theorem calculation_all (u : B) (h1 : mul u u ≠ 0) (v : B)
    (h2 : mul v v = mul u u) (h3 : mul v u = mul (inv u) v) (r : B)
    (h4 : mul r r = 0) (h5 : mul r u = mul u r) (h6 : mul r v = mul v r) (s : B)
    (h7 : mul s s = 0) (h8 : mul s u = mul u s) (h9 : mul s v = mul v s)
    (h10 : mul s r = mul (mul (mul u u) r) s)
    (hi : Outside.invol u v r s) (hm : moved u v r s = 4) :
    (all.map fun x => if word u v r s x == x then (1 : BitVec 6) else 0).sum = 4 := by
  have hall : ∀ x : B, x ∈ all := by decide +kernel
  have hu := List.all_eq_true.mp check_eq_true u (hall u)
  have hv := List.all_eq_true.mp (by simpa only [Bool.or_eq_true, beq_iff_eq,
    h1, false_or] using hu) v (hall v)
  simp only [h2, h3, bne_self_eq_false, Bool.false_or] at hv
  have hr := List.all_eq_true.mp hv r (hall r)
  simp only [h4, h5, h6, bne_self_eq_false, Bool.false_or] at hr
  have hs := List.all_eq_true.mp hr s (hall s)
  simpa only [h7, h8, h9, h10, hi, hm, bne_self_eq_false, Bool.false_or,
    Bool.not_true, beq_iff_eq] using hs
end J2OutsideSizesCalculation
