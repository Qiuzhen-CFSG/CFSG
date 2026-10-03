module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.GroupAction.FixedPoints
public import Mathlib.Tactic.Group

/-!
# Conjugacy of fixed elements under a coprime prime-power action

If a p-group acts on a finite group K of order prime to p, two fixed elements
conjugate in K have a fixed conjugator. The transporter is a coset of the
centralizer, so its cardinality divides |K|. The p-group fixed-point congruence
then supplies a fixed point in that transporter. In particular, when the fixed
subgroup is abelian, distinct fixed elements cannot fuse in K.

This is the elementary transporter proof of coprime fixed-point conjugacy.
-/

namespace Theory.GroupAction
open Subgroup MulAction

/-- Fixed conjugate elements have a fixed conjugator when a prime-power actor
acts on a finite group whose order is prime to that prime. -/
public theorem exists_fixed_conjugator_of_prime_not_dvd_card
    {A K : Type*} [Group A] [Group K] [Finite K]
    [MulDistribMulAction A K] {p : ℕ} [Fact p.Prime]
    (hA : IsPGroup p A) (hK : ¬ p ∣ Nat.card K)
    (x y : K) (hx : ∀ a : A, a • x = x) (hy : ∀ a : A, a • y = y)
    (hxy : IsConj x y) :
    ∃ k : K, (∀ a : A, a • k = k) ∧ k * x * k⁻¹ = y := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy
  let T := {k : K // k * x * k⁻¹ = y}
  let C := centralizer ({x} : Set K)
  let e : C ≃ T := {
    toFun c := ⟨g * c, by
      calc
        (g * c) * x * (g * c)⁻¹ = g * ((c : K) * x * (c : K)⁻¹) * g⁻¹ := by group
        _ = y := by
          rw [mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp c.property), hg]⟩
    invFun k := ⟨g⁻¹ * k, mem_centralizer_singleton_iff.mpr (by
      apply mul_inv_eq_iff_eq_mul.mp
      calc
        (g⁻¹ * k) * x * (g⁻¹ * k)⁻¹ = g⁻¹ * ((k : K) * x * (k : K)⁻¹) * g := by group
        _ = g⁻¹ * y * g := by rw [k.property]
        _ = x := by rw [← hg]; group)⟩
    left_inv c := Subtype.ext (by simp)
    right_inv k := Subtype.ext (by simp) }
  let _ : MulAction A T := {
    smul a k := ⟨a • (k : K), by
      calc
        (a • (k : K)) * x * (a • (k : K))⁻¹ =
            a • ((k : K) * x * (k : K)⁻¹) := by
          rw [smul_mul', smul_mul', smul_inv', hx a]
        _ = y := by rw [k.property, hy a]⟩
    one_smul k := Subtype.ext (one_smul A (k : K))
    mul_smul a b k := Subtype.ext (mul_smul a b (k : K)) }
  have hT : ¬ p ∣ Nat.card T := by
    rw [← Nat.card_congr e]
    exact fun h => hK (h.trans C.card_subgroup_dvd_card)
  obtain ⟨k, hk⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card T hT
  exact ⟨k, fun a => congrArg Subtype.val (hk a), k.property⟩

/-- If the fixed subgroup is abelian, distinct fixed elements cannot fuse
under conjugation in the whole group. -/
public theorem eq_of_isConj_of_fixed_of_isMulCommutative
    {A K : Type*} [Group A] [Group K] [Finite K]
    [MulDistribMulAction A K] {p : ℕ} [Fact p.Prime]
    (hA : IsPGroup p A) (hK : ¬ p ∣ Nat.card K)
    [IsMulCommutative (FixedPoints.subgroup A K)]
    (x y : K) (hx : ∀ a : A, a • x = x) (hy : ∀ a : A, a • y = y)
    (hxy : IsConj x y) : x = y := by
  obtain ⟨k, hk, he⟩ :=
    exists_fixed_conjugator_of_prime_not_dvd_card hA hK x y hx hy hxy
  have hc : k * x = x * k := congrArg Subtype.val
    (mul_comm' (⟨k, hk⟩ : FixedPoints.subgroup A K) ⟨x, hx⟩)
  simpa only [hc, mul_inv_cancel_right] using he

end Theory.GroupAction
