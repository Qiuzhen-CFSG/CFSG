module

public import Theory.Mathieu.M22.UniversalMultiplier.CyclicFour.WordCertificates.Action
public import Theory.Mathieu.M22.UniversalMultiplier.CyclicFour.WordCertificates.Verify

/-!
# Short generator relations and intermediate word actions

The kernel checks A² = B⁴ = 1 on every point of the original ATLAS action.
It also checks the lookup tables for AB and ABABB, so the longer order-eleven
checks can use short lookup expressions. `Action` identifies A and B with the
published literal permutations; no alternative group is substituted.

Source application: the perfect-cover construction for Aschbacher–Smith I.1.3(4).
-/

namespace Sporadic.Mathieu.M22CyclicFour.WordCertificates

set_option maxRecDepth 20000 in
private theorem a_square_checked : checkEq (iter (action a) 2) id = true := by
  decide +kernel

set_option maxRecDepth 20000 in
private theorem b_fourth_checked : checkEq (iter (action b) 4) id = true := by
  decide +kernel

set_option maxRecDepth 20000 in
private theorem ab_checked : checkEq (fun i => action a (action b i)) (action ab) = true := by
  decide +kernel

set_option maxRecDepth 20000 in
private theorem ababb_checked :
    checkEq (fun i => action ab (action ab (action b i))) (action ababb) = true := by
  decide +kernel

public theorem aPerm_sq : Data.aPerm ^ 2 = 1 :=
  pow_eq_one_of_check _ _ a_apply 2 a_square_checked

public theorem bPerm_four : Data.bPerm ^ 4 = 1 :=
  pow_eq_one_of_check _ _ b_apply 4 b_fourth_checked

public theorem ab_apply (i : Fin 4928) : (Data.aPerm * Data.bPerm) i = action ab i := by
  rw [Equiv.Perm.mul_apply, a_apply, b_apply]
  exact eq_of_check _ _ ab_checked i

public theorem ababb_apply (i : Fin 4928) :
    (Data.aPerm * Data.bPerm * Data.aPerm * Data.bPerm * Data.bPerm) i = action ababb i := by
  rw [mul_assoc (Data.aPerm * Data.bPerm) Data.aPerm Data.bPerm,
    Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ab_apply, ab_apply, b_apply]
  exact eq_of_check _ _ ababb_checked i

end Sporadic.Mathieu.M22CyclicFour.WordCertificates
