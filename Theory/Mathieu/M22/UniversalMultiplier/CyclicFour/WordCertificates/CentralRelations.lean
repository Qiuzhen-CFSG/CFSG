module

public import Theory.Mathieu.M22.UniversalMultiplier.CyclicFour.WordCertificates.CentralActions

/-!
# Exact quartic order and generator commutation in the ATLAS action

For the literal word Z = (ABABAB⁻¹)⁵, check Z⁴ = 1 and commutation with A and B
on all 4928 points. A single point moved by Z² excludes orders one and two.
These certificates concern the published permutations, not an abstract group
with assumed centrality or order.

Source application: Aschbacher–Smith I.1.3(4), through the paired-cover assembly.
-/

namespace Sporadic.Mathieu.M22CyclicFour.WordCertificates

private theorem commute_of_actions (p q : Equiv.Perm (Fin 4928))
    (f g : Fin 4928 → Fin 4928) (hp : ∀ i, p i = f i) (hq : ∀ i, q i = g i)
    (hc : checkEq (fun i => f (g i)) (fun i => g (f i)) = true) : Commute p q := by
  apply Equiv.ext
  intro i
  simp only [Equiv.Perm.mul_apply, hp, hq]
  exact eq_of_check _ _ hc i


set_option maxRecDepth 20000 in
private theorem z_fourth_checked : checkEq (iter (action z) 4) id = true := by
  decide +kernel

set_option maxRecDepth 20000 in
private theorem za_checked :
    checkEq (fun i => action z (action a i)) (fun i => action a (action z i)) = true := by
  decide +kernel

set_option maxRecDepth 20000 in
private theorem zb_checked :
    checkEq (fun i => action z (action b i)) (fun i => action b (action z i)) = true := by
  decide +kernel

public theorem centralPerm_four : centralPerm ^ 4 = 1 :=
  pow_eq_one_of_check _ _ centralPerm_apply 4 z_fourth_checked

public theorem centralPerm_sq_ne_one : centralPerm ^ 2 ≠ 1 := by
  intro h
  have h0 := congrArg (fun p : Equiv.Perm (Fin 4928) => p 0) h
  have hn : iter (action z) 2 0 ≠ 0 := by decide +kernel
  exact hn ((pow_action _ _ centralPerm_apply 2 0).symm.trans h0)

public theorem centralPerm_commute_a : Commute centralPerm Data.aPerm :=
  commute_of_actions _ _ _ _ centralPerm_apply a_apply za_checked

public theorem centralPerm_commute_b : Commute centralPerm Data.bPerm :=
  commute_of_actions _ _ _ _ centralPerm_apply b_apply zb_checked

end Sporadic.Mathieu.M22CyclicFour.WordCertificates
