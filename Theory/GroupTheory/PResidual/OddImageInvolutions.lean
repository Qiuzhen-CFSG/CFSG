module
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.OddOrderSquare

/-!
# Involutions in residuals with odd image

A homomorphism sends the two-residual into the two-residual of its target.
If that target residual has odd order, every square-one element of the
original residual lies in the kernel. This is the quotient step in the
fixed-seed case of Aschbacher--Smith 14.3.21(2), printed p.998.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G K : Type*} [Group G] [Group K]

theorem map_eq_one_of_square_one_mem_twoResidual
    (f : G →* K) (hodd : Odd (Nat.card (pResidual 2 K)))
    (x : G) (hx : x ∈ pResidual 2 G) (hx2 : x ^ 2 = 1) : f x = 1 := by
  have hm : f x ∈ pResidual 2 K := map_pResidual_le 2 f (mem_map_of_mem f hx)
  let a : pResidual 2 K := ⟨f x, hm⟩
  have ha : Odd (orderOf a) := hodd.of_dvd_nat (orderOf_dvd_natCard a)
  have ha2 : a ^ 2 = (1 : pResidual 2 K) ^ 2 := by
    apply Subtype.ext
    change (f x) ^ 2 = (1 : K) ^ 2
    rw [← map_pow, hx2, map_one, one_pow]
  exact congrArg Subtype.val
    (eq_of_sq_eq_sq_of_odd_orderOf ha (by simp) ha2)

end Theory.GroupTheory
