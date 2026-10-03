module

public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group

/-!
# Squares of inverters of a self-centralizing subgroup

Two inverters of a self-centralizing subgroup differ by an element of that
subgroup, and multiplying an inverter by such an element preserves its square.
Consequently, if the subgroup is characteristic, every automorphism fixes the
square of each inverter.

This isolates the characteristic-base argument used in MacWilliams,
Trans. Amer. Math. Soc. 150 (1970), §4, (ii) and (xviii), printed pp.387 and 396.
-/

open Subgroup
namespace Subgroup
/-- Two inverters of a self-centralizing subgroup have the same square. -/
public theorem sq_eq_of_inverters_of_centralizer_le
    {G : Type*} [Group G] (A : Subgroup G)
    (hA : centralizer (A : Set G) ≤ A) (s t : G)
    (hs : ∀ a ∈ A, s * a * s⁻¹ = a⁻¹)
    (ht : ∀ a ∈ A, t * a * t⁻¹ = a⁻¹) : s ^ 2 = t ^ 2 := by
  have hd : s * t⁻¹ ∈ A := by
    apply hA
    intro a ha
    have hit : t⁻¹ * a * t = a⁻¹ := by
      calc
        t⁻¹ * a * t = t⁻¹ * (t * a⁻¹ * t⁻¹) * t := by rw [ht _ (A.inv_mem ha), inv_inv]
        _ = a⁻¹ := by group
    have hc : (s * t⁻¹) * a * (s * t⁻¹)⁻¹ = a := by
      calc
        (s * t⁻¹) * a * (s * t⁻¹)⁻¹ = s * (t⁻¹ * a * t) * s⁻¹ := by group
        _ = a := by rw [hit, hs _ (A.inv_mem ha), inv_inv]
    exact (mul_inv_eq_iff_eq_mul.mp hc).symm
  calc
    s ^ 2 = (s * t⁻¹) * (t * (s * t⁻¹) * t⁻¹) * t ^ 2 := by simp only [pow_two]; group
    _ = t ^ 2 := by rw [ht _ hd, mul_inv_cancel, one_mul]

/-- Automorphisms fix the square of an inverter of a characteristic
self-centralizing subgroup. -/
public theorem automorphism_sq_eq_of_characteristic_inverted
    {G : Type*} [Group G] (A : Subgroup G) [A.Characteristic]
    (hA : centralizer (A : Set G) ≤ A) (t : G)
    (ht : ∀ a ∈ A, t * a * t⁻¹ = a⁻¹) (α : MulAut G) :
    α (t ^ 2) = t ^ 2 := by
  rw [map_pow]
  apply sq_eq_of_inverters_of_centralizer_le A hA (α t) t _ ht
  intro a ha
  have hpre : α.symm a ∈ A := characteristic_iff_le_comap.mp inferInstance α.symm ha
  have he := congrArg α (ht _ hpre)
  simpa only [map_mul, map_inv, α.apply_symm_apply] using he
end Subgroup
