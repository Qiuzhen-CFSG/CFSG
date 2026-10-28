module
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Involutions projected off a central direct factor

If commuting subgroups Z and R have trivial intersection, an involution
in ZR has involutory components. When Z centralizes K, its R component
normalizes K and induces the same conjugation on K as the original element.
The proof extracts the actual product coordinates and puts their squares
in Z ∩ R. No finiteness or quotient-lifting hypothesis is needed.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
the central reflection change in (14.17), printed p.222. Its universal-tree
application is `DGS85/ApartmentExchange/SixPathReflectionChange`.
-/

public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- Project an involution to the second factor, retaining its action on K. -/
theorem exists_involution_factor_of_central_product
    (Z R K : Subgroup G) (hZR : Z ≤ centralizer (R : Set G))
    (hZK : Z ≤ centralizer (K : Set G)) (hdis : Z ⊓ R = ⊥)
    (t : G) (ht : t ∈ Z ⊔ R) (ht2 : t*t=1)
    (htK : t ∈ normalizer (K : Set G)) :
    ∃ z ∈ Z, ∃ u ∈ R, t=z*u ∧ z*z=1 ∧ u*u=1 ∧
      u ∈ normalizer (K : Set G) ∧
      (∀ k ∈ K, u*k*u⁻¹=t*k*t⁻¹) := by
  have hp : t ∈ (Z : Set G) * (R : Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right Z R
      (hZR.trans (centralizer_le_normalizer _))]
    exact ht
  obtain ⟨z,hz,u,hu,htu⟩ := hp
  change z*u=t at htu
  have hcomm : Commute z u := ((hZR hz) u hu).symm
  have hprod : (z*z)*(u*u)=1 := by
    calc
      (z*z)*(u*u) = (z*u)*(z*u) := by
        simpa only [pow_two] using (hcomm.mul_pow 2).symm
      _ = 1 := by rw [htu,ht2]
  have hz2 : z*z=1 := hdis.le ⟨Z.mul_mem hz hz, by
    have he : z*z=(u*u)⁻¹ := eq_inv_of_mul_eq_one_left hprod
    rw [he]
    exact R.inv_mem (R.mul_mem hu hu)⟩
  have hu2 : u*u=1 := by simpa only [hz2,one_mul] using hprod
  have hue : u=z⁻¹*t := by rw [←htu,inv_mul_cancel_left]
  have huK : u ∈ normalizer (K : Set G) := by
    rw [hue]
    exact (normalizer (K : Set G)).mul_mem
      ((normalizer (K : Set G)).inv_mem (centralizer_le_normalizer _ (hZK hz))) htK
  refine ⟨z,hz,u,hu,htu.symm,hz2,hu2,huK,?_⟩
  intro k hk
  have hmem : u*k*u⁻¹ ∈ K := (mem_normalizer_iff.mp huK k).mp hk
  have hzcomm := (hZK hz) (u*k*u⁻¹) hmem
  rw [←htu,mul_inv_rev]
  calc
    u*k*u⁻¹ = (u*k*u⁻¹)*z*z⁻¹ := (mul_inv_cancel_right _ z).symm
    _ = z*(u*k*u⁻¹)*z⁻¹ := by rw [hzcomm]
    _ = z*u*k*(u⁻¹*z⁻¹) := by simp only [mul_assoc]

end Theory.GroupTheory
