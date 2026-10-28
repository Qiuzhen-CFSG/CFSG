module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.Algebra.Group.Conj

/-!
# The preserved axis of an outer quaternion involution

An involutory outer automorphism of the quaternion group of order eight
inverts every noncentral element whose coset modulo the center is fixed.
Each such element is also a displacement `x⁻¹ * e x`.

The proof writes an automorphism using its two generator images. A finite,
kernel-checked table verifies the assertion for these normal-form maps;
the result is then transported through a quaternion isomorphism.

This is the quaternion-action calculation in Janko–Thompson (1970), §4,
Case 2, printed p.393, used for displacement in a quaternion–cyclic
central product.
-/

namespace QuaternionGroup
private abbrev K := QuaternionGroup 2
private def axisMap (p : K × K) : K → K
  | a i => p.1 ^ i.val
  | xa i => p.2 * p.1 ^ i.val

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem axis_table : ∀ p : K × K,
    (∀ x y : K, axisMap p (x*y) = axisMap p x * axisMap p y) →
    (∀ x : K, axisMap p (axisMap p x) = x) →
    (¬ ∃ z : K, ∀ x : K, axisMap p x = z * x * z⁻¹) →
    ∀ q : K, (¬ ∀ y : K, y * q = q * y) →
      (∀ y : K, y * (q⁻¹ * axisMap p q) = (q⁻¹ * axisMap p q) * y) →
      axisMap p q = q⁻¹ ∧ ∃ x : K, x⁻¹ * axisMap p x = q := by
  decide

/-- A preserved noncentral quaternion axis is inverted by an outer involution,
and its generators occur as displacements. -/
public theorem outer_involution_axis (e : MulAut (QuaternionGroup 2))
    (he : e ^ 2 = 1) (ho : ¬ ∃ z, e = MulAut.conj z)
    (q : QuaternionGroup 2) (hq : q ∉ Subgroup.center (QuaternionGroup 2))
    (hd : q⁻¹ * e q ∈ Subgroup.center (QuaternionGroup 2)) :
    e q = q⁻¹ ∧ ∃ x, x⁻¹ * e x = q := by
  let p : K × K := (e (a 1), e (xa 0))
  have hp (x : K) : axisMap p x = e x := by
    cases x with
    | a i =>
      change (e (a 1)) ^ i.val = e (a i)
      rw [← map_pow, a_one_pow, ZMod.natCast_zmod_val]
    | xa i =>
      change e (xa 0) * (e (a 1)) ^ i.val = e (xa i)
      rw [← map_pow, ← map_mul, a_one_pow, ZMod.natCast_zmod_val, xa_mul_a, zero_add]
  have hm : ∀ x y : K, axisMap p (x*y) = axisMap p x * axisMap p y := by
    simp only [hp, map_mul, implies_true]
  have hi : ∀ x : K, axisMap p (axisMap p x) = x := by
    intro x
    simpa only [hp, pow_two, MulAut.mul_apply, MulAut.one_apply] using
      DFunLike.congr_fun he x
  have hn : ¬ ∃ z : K, ∀ x : K, axisMap p x = z * x * z⁻¹ := by
    rintro ⟨z, hz⟩
    apply ho
    refine ⟨z, ?_⟩
    ext x
    exact (hp x).symm.trans (hz x)
  simpa only [hp] using axis_table p hm hi hn q
    (fun h => hq (Subgroup.mem_center_iff.mpr h))
    (by simpa only [hp] using Subgroup.mem_center_iff.mp hd)

/-- The outer-involution axis calculation transported through an isomorphism. -/
public theorem outer_involution_axis_of_equiv {G : Type*} [Group G]
    (model : G ≃* QuaternionGroup 2) (e : MulAut G)
    (he : e ^ 2 = 1) (ho : ¬ ∃ z, e = MulAut.conj z)
    (q : G) (hq : q ∉ Subgroup.center G)
    (hd : q⁻¹ * e q ∈ Subgroup.center G) :
    e q = q⁻¹ ∧ ∃ x, x⁻¹ * e x = q := by
  let a := MulAut.congr model e
  have ha : a ^ 2 = 1 := by dsimp [a]; rw [← map_pow, he, map_one]
  have ho' : ¬ ∃ z, a = MulAut.conj z := by
    rintro ⟨z, hz⟩
    apply ho
    refine ⟨model.symm z, ?_⟩
    ext x
    apply model.injective
    have h := DFunLike.congr_fun hz (model x)
    simpa [a, MulAut.congr_apply, MulAut.conj_apply] using h
  have hq' : model q ∉ Subgroup.center (QuaternionGroup 2) := by
    intro h
    apply hq
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply model.injective
    simpa only [map_mul] using Subgroup.mem_center_iff.mp h (model y)
  have hd' : (model q)⁻¹ * a (model q) ∈ Subgroup.center (QuaternionGroup 2) := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨z, rfl⟩ := model.surjective y
    simpa [a, MulAut.congr_apply] using
      congrArg model (Subgroup.mem_center_iff.mp hd z)
  obtain ⟨hinv, x, hx⟩ := outer_involution_axis a ha ho' (model q) hq' hd'
  constructor
  · apply model.injective
    simpa [a, MulAut.congr_apply] using hinv
  · refine ⟨model.symm x, ?_⟩
    apply model.injective
    simpa [a, MulAut.congr_apply] using hx
end QuaternionGroup
