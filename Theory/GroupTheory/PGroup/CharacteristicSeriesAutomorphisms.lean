module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Automorphisms acting trivially along a characteristic series

For a finite p-group G and characteristic subgroups C and D, automorphisms
whose displacements send G into C, C into D, and D to the identity form a
normal p-subgroup. No assumption that D is characteristic in C is needed.

If G has exponent dividing p^k, a first p^k-th power fixes C pointwise and
a second fixes G pointwise. The displacement identity proves this directly,
without assuming commutativity or constructing quotient actions.

Source: the elementary characteristic-series automorphism-kernel argument,
used here for the local obstructions in the Ree two Sylow model.
-/

namespace Subgroup
variable {G : Type*} [Group G]

/-- Automorphisms whose displacement on C lies in D. -/
@[expose] public def characteristicStepKernel (C D : Subgroup G) [C.Characteristic] [D.Characteristic] :
    Subgroup (MulAut G) where
  carrier := {f | ∀ x ∈ C, x⁻¹ * f x ∈ D}
  one_mem' := by intro x _; simp
  mul_mem' := by
    intro f g hf hg x hx
    have hd := characteristic_iff_le_comap.mp (inferInstance : D.Characteristic) f (hg x hx)
    change f (x⁻¹ * g x) ∈ D at hd
    have he : x⁻¹ * (f * g) x = (x⁻¹ * f x) * f (x⁻¹ * g x) := by
      simp [map_mul, map_inv, mul_assoc]
    rw [he]
    exact D.mul_mem (hf x hx) hd
  inv_mem' := by
    intro f hf x hx
    have hc := characteristic_iff_le_comap.mp (inferInstance : C.Characteristic) f⁻¹ hx
    have hd := hf (f⁻¹ x) hc
    simpa using D.inv_mem hd

public instance characteristicStepKernel_normal (C D : Subgroup G)
    [C.Characteristic] [D.Characteristic] : (characteristicStepKernel C D).Normal where
  conj_mem f hf a := by
    intro x hx
    have hc := characteristic_iff_le_comap.mp (inferInstance : C.Characteristic) a⁻¹ hx
    have hd := characteristic_iff_le_comap.mp (inferInstance : D.Characteristic) a
      (hf (a⁻¹ x) hc)
    simpa [map_mul, map_inv] using hd

private lemma pow_apply_of_fixed_displacement (f : MulAut G) (x : G)
    (h : f (x⁻¹ * f x) = x⁻¹ * f x) (n : ℕ) :
    (f ^ n) x = x * (x⁻¹ * f x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, h, pow_succ']
    simp [mul_assoc]

/-- The kernel of a three-step characteristic-series action is a p-group. -/
public theorem isPGroup_threeStepKernel [Finite G] {p : ℕ}
    (hG : IsPGroup p G) (C D : Subgroup G) [C.Characteristic] [D.Characteristic] :
    IsPGroup p ↥(characteristicStepKernel ⊤ C ⊓ characteristicStepKernel C D ⊓
      characteristicStepKernel D ⊥) := by
  obtain ⟨k, hk⟩ := isPGroup_iff_exists_pow_pow_eq_one.mp hG
  intro a
  let f : MulAut G := a
  have hc : ∀ x ∈ C, (f ^ (p ^ k)) x = x := by
    intro x hx
    have hd := a.property.1.2 x hx
    have hf : f (x⁻¹ * f x) = x⁻¹ * f x := by
      have hh := a.property.2 (x⁻¹ * f x) hd
      change (x⁻¹ * f x)⁻¹ * f (x⁻¹ * f x) = 1 at hh
      exact (inv_mul_eq_one.mp hh).symm
    rw [pow_apply_of_fixed_displacement f x hf, hk, mul_one]
  have hpow := (characteristicStepKernel ⊤ C).pow_mem a.property.1.1 (p ^ k)
  have he : (f ^ (p ^ k)) ^ (p ^ k) = 1 := by
    ext x
    have hd : x⁻¹ * (f ^ (p ^ k)) x ∈ C := hpow x (mem_top x)
    rw [pow_apply_of_fixed_displacement _ x (hc _ hd), hk, mul_one]
    rfl
  refine ⟨k + k, Subtype.ext ?_⟩
  change f ^ (p ^ (k + k)) = 1
  rw [pow_add, pow_mul]
  exact he

/-- The kernel of a four-step characteristic-series action is a p-group. -/
public theorem isPGroup_fourStepKernel [Finite G] {p : ℕ}
    (hG : IsPGroup p G) (C D E : Subgroup G)
    [C.Characteristic] [D.Characteristic] [E.Characteristic] :
    IsPGroup p ↥(characteristicStepKernel ⊤ C ⊓ characteristicStepKernel C D ⊓
      characteristicStepKernel D E ⊓ characteristicStepKernel E ⊥) := by
  obtain ⟨k, hk⟩ := isPGroup_iff_exists_pow_pow_eq_one.mp hG
  intro a
  let f : MulAut G := a
  have he : ∀ x ∈ E, f x = x := by
    intro x hx
    have hh := a.property.2 x hx
    change x⁻¹ * f x = 1 at hh
    exact (inv_mul_eq_one.mp hh).symm
  have hd : ∀ x ∈ D, (f ^ (p ^ k)) x = x := by
    intro x hx
    rw [pow_apply_of_fixed_displacement f x (he _ (a.property.1.2 x hx)), hk, mul_one]
  have hc : ∀ x ∈ C, ((f ^ (p ^ k)) ^ (p ^ k)) x = x := by
    intro x hx
    have hpow := (characteristicStepKernel C D).pow_mem a.property.1.1.2 (p ^ k)
    rw [pow_apply_of_fixed_displacement _ x (hd _ (hpow x hx)), hk, mul_one]
  have hpow := (characteristicStepKernel ⊤ C).pow_mem
    ((characteristicStepKernel ⊤ C).pow_mem a.property.1.1.1 (p ^ k)) (p ^ k)
  have hh : ((f ^ (p ^ k)) ^ (p ^ k)) ^ (p ^ k) = 1 := by
    ext x
    rw [pow_apply_of_fixed_displacement _ x (hc _ (hpow x (mem_top x))), hk, mul_one]
    rfl
  refine ⟨k + k + k, Subtype.ext ?_⟩
  change f ^ (p ^ (k + k + k)) = 1
  simpa only [pow_add, pow_mul] using hh

end Subgroup
