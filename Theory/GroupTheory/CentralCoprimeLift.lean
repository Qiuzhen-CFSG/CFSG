module
public import Mathlib.GroupTheory.PGroup

/-!
# Coprime power lifts across central p-group kernels

A surjective homomorphism with central p-group kernel lifts an element
satisfying y^n=1 to an element with the same power relation whenever n is
coprime to p. No finiteness or exact element order is required.

The nth power of any lift lies in the kernel. The coprime power bijection
on that kernel supplies its unique nth root; multiplying the lift by the
inverse root removes the unwanted power, since the kernel is central.
This elementary construction supplies the order-three lift in the q=3
central-cover argument of ABG II.3 Proposition 2.
-/

namespace MonoidHom

public theorem exists_pow_eq_one_lift_of_central_pgroup_ker
    {E Q : Type*} [Group E] [Group Q] (q : E →* Q)
    (hq : Function.Surjective q) (hcenter : q.ker ≤ Subgroup.center E)
    {p n : ℕ} (hp : IsPGroup p q.ker) (hcoprime : Nat.Coprime p n)
    (y : Q) (hy : y ^ n = 1) :
    ∃ x : E, q x = y ∧ x ^ n = 1 := by
  obtain ⟨x, hx⟩ := hq y
  have hxn : x ^ n ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_pow, hx, hy]
  obtain ⟨k, hk⟩ := (hp.powEquiv hcoprime).surjective ⟨x ^ n, hxn⟩
  have hkpow : (k : E) ^ n = x ^ n := congrArg Subtype.val hk
  have hkcomm : Commute x (k : E) :=
    Subgroup.mem_center_iff.mp (hcenter k.property) x
  refine ⟨x * (k : E)⁻¹, ?_, ?_⟩
  · simp only [map_mul, map_inv, show q (k : E) = 1 from k.property, inv_one,
      mul_one, hx]
  · rw [hkcomm.inv_right.mul_pow, inv_pow, hkpow, mul_inv_cancel]

end MonoidHom
