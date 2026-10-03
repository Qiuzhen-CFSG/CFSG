module

public import Theory.GroupTheory.CentralCoprimeLift

/-!
# Uniqueness of coprime torsion lifts through central prime-power kernels

Two elements with the same image differ by a central kernel element.
Their equal coprime power relations force that difference to be trivial.
Consequently conjugation and inversion relations between coprime torsion
lifts can be checked in the quotient.
-/

namespace MonoidHom

public theorem eq_of_map_eq_of_pow_eq_one_of_central_pgroup_ker
    {E Q : Type*} [Group E] [Group Q] (q : E →* Q)
    (hcenter : q.ker ≤ Subgroup.center E) {p n : ℕ}
    (hp : IsPGroup p q.ker) (hcoprime : Nat.Coprime p n)
    {x y : E} (hxy : q x = q y) (hx : x ^ n = 1) (hy : y ^ n = 1) : x = y := by
  have hk : x * y⁻¹ ∈ q.ker := by simp [MonoidHom.mem_ker, hxy]
  have hc : Commute (x * y⁻¹) y :=
    (Subgroup.mem_center_iff.mp (hcenter hk) y).symm
  have hcomm : Commute x y := by
    have hh := hc.mul_left (Commute.refl y)
    simpa only [inv_mul_cancel_right] using hh
  have hpow : (x * y⁻¹) ^ n = 1 := by
    rw [hcomm.inv_right.mul_pow, hx, inv_pow, hy, inv_one, one_mul]
  have heq : (⟨x * y⁻¹, hk⟩ : q.ker) = 1 := by
    apply (hp.powEquiv hcoprime).injective
    exact Subtype.ext (by simpa using hpow)
  exact mul_inv_eq_one.mp (congrArg Subtype.val heq)

end MonoidHom
