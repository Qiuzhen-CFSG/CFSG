module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Tactic

/-!
# Automorphisms on involutions of C₄ × C₄

The automorphism (a,b) ↦ (b⁻¹,ab⁻¹) cycles the three involutions.
Its inverse is explicit; the coordinate identities and its three-element
orbit are checked in the kernel on the finite model. Transport along an
isomorphism proves transitivity for any group equivalent to C₄ × C₄.

This elementary calculation supplies the normal-base automorphism step
in Janko–Thompson, Math. Z. 113 (1970), 1.4 and p.395.
-/


private abbrev Model := Multiplicative (ZMod 4) × Multiplicative (ZMod 4)
private def rotate : MulAut Model where
  toFun x := (x.2⁻¹, x.1 * x.2⁻¹)
  invFun x := (x.2 * x.1⁻¹, x.1⁻¹)
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

set_option synthInstance.maxSize 1024 in
private theorem three_images : ∀ x y : Model,
    x ^ 2 = 1 → x ≠ 1 → y ^ 2 = 1 → y ≠ 1 →
    x = y ∨ rotate x = y ∨ rotate (rotate x) = y := by decide +kernel

public theorem MulEquiv.involutions_transitive_of_c4_square
    {D : Type*} [Group D]
    (e : D ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))
    (x y : D) (hx : orderOf x = 2) (hy : orderOf y = 2) :
    ∃ a : MulAut D, a x = y := by
  have hxp : (e x) ^ 2 = 1 := by rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  have hyp : (e y) ^ 2 = 1 := by rw [← map_pow, ← hy, pow_orderOf_eq_one, map_one]
  have hxne : e x ≠ 1 := by
    intro h
    have h' : x = 1 := e.injective (h.trans (map_one e).symm)
    simp [h'] at hx
  have hyne : e y ≠ 1 := by
    intro h
    have h' : y = 1 := e.injective (h.trans (map_one e).symm)
    simp [h'] at hy
  rcases three_images (e x) (e y) hxp hxne hyp hyne with h | h | h
  · exact ⟨1, e.injective h⟩
  · refine ⟨e.trans (rotate.trans e.symm), ?_⟩
    change e.symm (rotate (e x)) = y
    rw [h, e.symm_apply_apply]
  · refine ⟨e.trans ((rotate.trans rotate).trans e.symm), ?_⟩
    change e.symm (rotate (rotate (e x))) = y
    rw [h, e.symm_apply_apply]
