module

public import Theory.GroupTheory.CentralCoprimeLiftUnique

/-!
# Lifting the squaring automorphism of a cyclic five-subgroup

Across a central three-group kernel, lift a fifth root of one using coprime
power lifting. Any lift of an element conjugating it to its square has the
same property, by uniqueness of fifth roots of one in a fixed coset.
The argument does not require a splitting of the whole extension.

Source application: the A₇ and central three-cover exclusions in
Aschbacher–Smith, E.6.18, combined manuscript (1 March 2004), printed p.252.
-/

public section

open Subgroup
namespace MonoidHom

/-- The order-five squaring relation lifts through a central three-group kernel. -/
theorem exists_five_cycle_square_lift
    {E Q : Type*} [Group E] [Group Q] (q : E →* Q)
    (hq : Function.Surjective q) (hz : q.ker ≤ center E)
    (hk : IsPGroup 3 q.ker) (x y : Q) (hx : orderOf x = 5)
    (hxy : y * x * y⁻¹ = x ^ 2) :
    ∃ a b : E, orderOf a = 5 ∧ b * a * b⁻¹ = a ^ 2 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hx5 : x ^ 5 = 1 := hx ▸ pow_orderOf_eq_one x
  obtain ⟨a, ha, ha5⟩ := q.exists_pow_eq_one_lift_of_central_pgroup_ker hq hz hk
    (by decide : Nat.Coprime 3 5) x hx5
  obtain ⟨b, hb⟩ := hq y
  have hane : a ≠ 1 := by
    intro h
    have hx1 : x = 1 := by rw [← ha, h, map_one]
    simp [hx1] at hx
  refine ⟨a, b, orderOf_eq_prime ha5 hane, ?_⟩
  apply q.eq_of_map_eq_of_pow_eq_one_of_central_pgroup_ker hz hk
    (by decide : Nat.Coprime 3 5)
  · simpa only [map_mul, map_inv, map_pow, ha, hb] using hxy
  · exact (map_pow (MulAut.conj b) a 5).symm.trans (by rw [ha5, map_one])
  · rw [pow_right_comm, ha5, one_pow]

end MonoidHom
