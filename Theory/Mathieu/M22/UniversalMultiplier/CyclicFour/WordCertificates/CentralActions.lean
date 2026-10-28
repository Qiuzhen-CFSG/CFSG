module

public import Theory.Mathieu.M22.UniversalMultiplier.CyclicFour.WordCertificates.BaseRelations

/-!
# The action of the distinguished central-word candidate

Check an inverse table for B, then the word W = ABABAB⁻¹ and Z = W⁵.
Every equality is checked on all 4928 points and transported to the original
ATLAS permutations through the proved generator-action bridge.

Source application: the cyclic-four cover in Aschbacher–Smith I.1.3(4).
-/

namespace Sporadic.Mathieu.M22CyclicFour.WordCertificates

set_option maxRecDepth 20000 in
private theorem bi_checked : checkEq (fun i => action b (action bi i)) id = true := by
  decide +kernel

set_option maxRecDepth 20000 in
private theorem w_checked :
    checkEq (fun i => action ab (action ab (action a (action bi i)))) (action w) = true := by
  decide +kernel

set_option maxRecDepth 20000 in
private theorem z_checked : checkEq (iter (action w) 5) (action z) = true := by
  decide +kernel

public theorem bi_apply (i : Fin 4928) : Data.bPerm⁻¹ i = action bi i := by
  apply Data.bPerm.injective
  calc
    Data.bPerm (Data.bPerm⁻¹ i) = i := by
      rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
    _ = action b (action bi i) := (eq_of_check _ _ bi_checked i).symm
    _ = _ := (b_apply _).symm

public theorem w_apply (i : Fin 4928) :
    (Data.aPerm * Data.bPerm * Data.aPerm * Data.bPerm * Data.aPerm * Data.bPerm⁻¹) i =
      action w i := by
  rw [mul_assoc (Data.aPerm * Data.bPerm) Data.aPerm Data.bPerm,
    Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    ab_apply, ab_apply, a_apply, bi_apply]
  exact eq_of_check _ _ w_checked i

@[expose] public noncomputable def centralPerm : Equiv.Perm (Fin 4928) :=
  (Data.aPerm * Data.bPerm * Data.aPerm * Data.bPerm * Data.aPerm * Data.bPerm⁻¹) ^ 5

public theorem centralPerm_apply (i : Fin 4928) : centralPerm i = action z i :=
  (pow_action _ _ w_apply 5 i).trans (eq_of_check _ _ z_checked i)

end Sporadic.Mathieu.M22CyclicFour.WordCertificates
