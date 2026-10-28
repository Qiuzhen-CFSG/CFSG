module
public import Theory.GroupTheory.QuaternionBinaryCentralExtension
import all Theory.GroupTheory.QuaternionBinaryCentralExtension

/-!
# Fixed lifts of the central quaternion involution

In a central extension of Q₈, its central involution has a distinguished
lift: the nonidentity element of the derived subgroup, which has order two.
Every automorphism fixes this element. If it also fixes the kernel pointwise,
it therefore fixes every lift of the quaternion involution. No restriction
on the exponent of the kernel is needed.

The internal import deliberately reuses the quaternion commutator calculation
in the parent module, separating its fixed-lift conclusion from the binary
kernel hypothesis needed only for its square conclusion. The normalizer
corollary applies to literal preimages under a central extension. Its M₁₂
consumer is `Theory.Mathieu.SchurMultipliers.M12Upper.Fusion`.
Source: the quaternion-factor lifting underlying Aschbacher–Smith I.2.2(5),
printed p.411, and the M₁₂ multiplier in I.1.3(1), printed p.407.
-/

open Subgroup
namespace MonoidHom

/-- Fixing the central kernel pointwise fixes every lift of the quaternion involution. -/
public theorem quaternion_lift_fixed_of_kernel_fixed {G : Type*} [Group G]
    (q : G →* QuaternionGroup 2) (hq : Function.Surjective q)
    (hk : q.ker ≤ center G) (x : G) (hx : q x = QuaternionGroup.a 2)
    (α : MulAut G) (hα : ∀ k ∈ q.ker, α k = k) : α x = x := by
  obtain ⟨a, ha⟩ := hq (QuaternionGroup.a 1)
  obtain ⟨b, hb⟩ := hq (QuaternionGroup.xa 0)
  exact QuaternionBinaryExtension.automorphism_fixes_lift q hk a b ha hb α hα x hx

/-- A lift of a quaternion normalizer centralizes every lift of its central involution. -/
public theorem commute_lift_of_quaternion_normalizer
    {E G : Type*} [Group E] [Group G]
    (f : E →* G) (hf : Function.Surjective f) (hk : f.ker ≤ center E)
    (Q : Subgroup G) (e : Q ≃* QuaternionGroup 2)
    (a x : E) (ha : f a ∈ normalizer (Q : Set G))
    (hx : f x ∈ Q) (hex : e ⟨f x, hx⟩ = QuaternionGroup.a 2) : Commute a x := by
  let P := Q.comap f
  let q : P →* QuaternionGroup 2 := e.toMonoidHom.comp (f.subgroupComap Q)
  have hq : Function.Surjective q := e.surjective.comp
    (f.subgroupComap_surjective_of_surjective Q hf)
  have hqk {y : P} (hy : y ∈ q.ker) : (y : E) ∈ f.ker := by
    have he : f.subgroupComap Q y = 1 := e.injective (hy.trans (map_one e).symm)
    exact congrArg Subtype.val he
  have hqc : q.ker ≤ center P := fun y hy => mem_center_iff.mpr fun t =>
    Subtype.ext (mem_center_iff.mp (hk (hqk hy)) t)
  have haP : a ∈ normalizer (P : Set E) := by
    rw [mem_normalizer_iff]
    intro y
    change f y ∈ Q ↔ f (a * y * a⁻¹) ∈ Q
    simpa only [map_mul, map_inv] using (mem_normalizer_iff.mp ha (f y))
  let α : MulAut P := P.normalizerMonoidHom ⟨a, haP⟩
  have hα : ∀ y ∈ q.ker, α y = y := by
    intro y hy
    apply Subtype.ext
    change a * (y : E) * a⁻¹ = y
    rw [mem_center_iff.mp (hk (hqk hy)) a, mul_inv_cancel_right]
  have he := quaternion_lift_fixed_of_kernel_fixed q hq hqc ⟨x, hx⟩ hex α hα
  have he' : a * x * a⁻¹ = x := congrArg Subtype.val he
  exact (mul_inv_eq_iff_eq_mul.mp he')

end MonoidHom
