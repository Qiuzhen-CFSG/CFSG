module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Coprime torsion lifts through central kernels

If the kernel order is coprime to m, its m-th power map is bijective.
Correcting an arbitrary preimage by a central kernel element gives the
unique lift satisfying x^m = 1. Conjugation preserves this unique lift,
so centralizing such an element can be checked in the quotient.

This is the finite-kernel step in Steinberg, *Lectures on Chevalley
Groups*, Theorem 11 (Section 7), used for the prime-to-characteristic
part of covering calculations. It extends the p-group-kernel arguments
in `CentralCoprimeLift` and `CentralCoprimeLiftUnique` to coprime kernel order.
-/

public section
namespace MonoidHom

variable {E Q : Type*} [Group E] [Group Q]

/-- Correct a lift by an m-th root in the central kernel. -/
theorem exists_pow_eq_one_lift_of_central_coprime_ker
    (f : E →* Q) (hf : Function.Surjective f)
    (hcenter : f.ker ≤ Subgroup.center E) {m : ℕ}
    (hcop : (Nat.card f.ker).Coprime m) (y : Q) (hy : y ^ m = 1) :
    ∃ x : E, f x = y ∧ x ^ m = 1 := by
  obtain ⟨x, hx⟩ := hf y
  have hxm : x ^ m ∈ f.ker := by rw [mem_ker, map_pow, hx, hy]
  obtain ⟨k, hk⟩ := (powCoprime hcop).surjective ⟨x ^ m, hxm⟩
  have hkpow : (k : E) ^ m = x ^ m := congrArg Subtype.val hk
  have hcomm : Commute x (k : E) := Subgroup.mem_center_iff.mp (hcenter k.property) x
  refine ⟨x * (k : E)⁻¹, ?_, ?_⟩
  · simp only [map_mul, map_inv, show f (k : E) = 1 from k.property,
      inv_one, mul_one, hx]
  · rw [hcomm.inv_right.mul_pow, inv_pow, hkpow, mul_inv_cancel]

/-- The coprime power relation makes a lift unique. -/
theorem eq_of_map_eq_of_pow_eq_one_of_central_coprime_ker
    (f : E →* Q) (hcenter : f.ker ≤ Subgroup.center E) {m : ℕ}
    (hcop : (Nat.card f.ker).Coprime m)
    {x y : E} (hxy : f x = f y) (hx : x ^ m = 1) (hy : y ^ m = 1) : x = y := by
  have hk : x * y⁻¹ ∈ f.ker := by simp [mem_ker, hxy]
  have hc : Commute (x * y⁻¹) y :=
    (Subgroup.mem_center_iff.mp (hcenter hk) y).symm
  have hcomm : Commute x y := by
    simpa only [inv_mul_cancel_right] using hc.mul_left (Commute.refl y)
  have hpow : (x * y⁻¹) ^ m = 1 := by
    rw [hcomm.inv_right.mul_pow, hx, inv_pow, hy, inv_one, one_mul]
  have heq : (⟨x * y⁻¹, hk⟩ : f.ker) = 1 := by
    apply (powCoprime hcop).injective
    exact Subtype.ext (by simpa using hpow)
  exact mul_inv_eq_one.mp (congrArg Subtype.val heq)

/-- A coprime torsion element centralizes every lift of its image's centralizer. -/
theorem commute_of_map_commute_of_pow_eq_one_of_central_coprime_ker
    (f : E →* Q) (hcenter : f.ker ≤ Subgroup.center E) {m : ℕ}
    (hcop : (Nat.card f.ker).Coprime m) {x y : E}
    (hx : x ^ m = 1) (hxy : Commute (f x) (f y)) : Commute x y := by
  have heq : y * x * y⁻¹ = x := by
    apply f.eq_of_map_eq_of_pow_eq_one_of_central_coprime_ker hcenter hcop _ _ hx
    · simp only [map_mul, map_inv]
      rw [hxy.symm.eq]
      simp [mul_assoc]
    · rw [conj_pow, hx]
      simp
  have h := congrArg (fun z => z * y) heq
  exact (show y * x = x * y by simpa only [inv_mul_cancel_right] using h).symm

end MonoidHom
