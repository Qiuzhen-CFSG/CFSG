module

public import Mathlib.GroupTheory.IsPerfect

/-!
# Normalizers of perfect subgroups through a central kernel

A perfect subgroup is contained in another subgroup whenever its image is
contained in that subgroup's image under a homomorphism with central kernel.
Indeed, replace both entries of each commutator by representatives in the
second subgroup; the central discrepancies disappear. Consequently the
normalizer of a perfect subgroup is exactly the inverse image of the
normalizer of its image. No ambient normality or surjectivity is needed.

This supplies the actual-subgroup transport in Aschbacher–Smith, 16.3.9,
printed p.1181: normalizing the image of a component modulo the center
really normalizes the component itself.
-/

public section

open Subgroup
open scoped commutatorElement

namespace Subgroup
variable {G D : Type*} [Group G] [Group D]

private theorem commutator_central_factors (kx ky x y : G)
    (hkx : kx ∈ center G) (hky : ky ∈ center G) :
    ⁅kx * x, ky * y⁆ = ⁅x,y⁆ := by
  have hx (z : G) : Commute kx z := (mem_center_iff.mp hkx z).symm
  have hy (z : G) : Commute ky z := (mem_center_iff.mp hky z).symm
  rw [commutatorElement_mul_left_eq_conj_mul, (hx (ky*y)).commutator_eq,
    mul_one, (hx ⁅x,ky*y⁆).eq, mul_inv_cancel_right,
    commutatorElement_mul_right_eq_mul_conj, (hy x).symm.commutator_eq,
    one_mul, (hy ⁅x,y⁆).eq, mul_inv_cancel_right]

/-- Perfect subgroups lift image containments across a central kernel. -/
theorem le_of_map_le_of_perfect (f : G →* D) (hker : f.ker ≤ center G)
    (H J : Subgroup G) [Group.IsPerfect H] (h : H.map f ≤ J.map f) : H ≤ J := by
  rw [← commutator_eq_self (H := H)]
  apply commutator_le.mpr
  intro x hx y hy
  obtain ⟨a, ha, hfa⟩ := h (mem_map_of_mem f hx)
  obtain ⟨b, hb, hfb⟩ := h (mem_map_of_mem f hy)
  have hkx : x * a⁻¹ ∈ center G := hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hfa, mul_inv_cancel])
  have hky : y * b⁻¹ ∈ center G := hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hfb, mul_inv_cancel])
  have he := commutator_central_factors (x*a⁻¹) (y*b⁻¹) a b hkx hky
  simp only [inv_mul_cancel_right] at he
  rw [he, commutatorElement_def]
  exact J.mul_mem (J.mul_mem (J.mul_mem ha hb) (J.inv_mem ha)) (J.inv_mem hb)

/-- Quotient normalization lifts to the actual perfect subgroup. -/
theorem comap_normalizer_map_eq_of_perfect (f : G →* D)
    (hker : f.ker ≤ center G) (L : Subgroup G) [Group.IsPerfect L] :
    (normalizer (L.map f : Set D)).comap f = normalizer (L : Set G) := by
  ext x
  change f x ∈ normalizer (L.map f : Set D) ↔ x ∈ normalizer (L : Set G)
  constructor
  · intro hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    let J := L.map (MulAut.conj x).toMonoidHom
    let : Group.IsPerfect J := Group.IsPerfect.map _
    have he : J.map f = L.map f := by
      calc
        _ = (L.map f).map (MulAut.conj (f x)).toMonoidHom := by
          rw [map_map, map_map]
          congr 1
          ext y
          simp [MulAut.conj_apply]
        _ = L.map f := mem_normalizer_iff_map_conj_eq.mp hx
    exact le_antisymm (le_of_map_le_of_perfect f hker J L he.le)
      (le_of_map_le_of_perfect f hker L J he.ge)
  · intro hx
    exact L.le_normalizer_map f (mem_map_of_mem f hx)

end Subgroup
