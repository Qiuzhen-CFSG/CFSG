module
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

/-!
# Central commutators of two involutions

If one involution belongs to the center of a subgroup normalized by another,
their nontrivial commutator is an involution central in the subgroup generated
by the normalized subgroup and the second involution. This is the elementary
group step in Goldschmidt (6.4), printed p.397.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

theorem central_commutator_of_normalizing_involutions
    (Q E : Subgroup G) {z x : G} (hzQ : z ∈ Q)
    (hzC : ∀ a ∈ Q, Commute z a) (hxN : x ∈ normalizer (Q : Set G))
    (hz2 : z ^ 2 = 1) (hx2 : x ^ 2 = 1)
    (hgen : E = Q ⊔ zpowers x) (hnc : ¬ Commute z x) :
    orderOf ⁅z, x⁆ = 2 ∧ ⁅z, x⁆ ∈ E ∧ ∀ a ∈ E, Commute ⁅z, x⁆ a := by
  let y := x * z * x⁻¹
  let u := ⁅z, x⁆
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hz2)
  have hu : u = z * y := by
    dsimp only [u, y]
    simp only [commutatorElement_def, hzi, mul_assoc]
  have hyQ : y ∈ Q := (Subgroup.mem_normalizer_iff.mp hxN z).1 hzQ
  have hyC : ∀ a ∈ Q, Commute y a := by
    intro a ha
    have ha' : x⁻¹ * a * x ∈ Q := (Subgroup.mem_normalizer_iff''.mp hxN a).1 ha
    have hc := (hzC _ ha').conj x
    simpa only [y, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_right, mul_inv_cancel, mul_one] using hc
  have hzy : Commute z y := hzC y hyQ
  have hy2 : y ^ 2 = 1 := by
    change ((MulAut.conj x) z) ^ 2 = 1
    rw [← map_pow, hz2, map_one]
  have hu2 : u ^ 2 = 1 := by rw [hu, hzy.mul_pow, hz2, hy2, one_mul]
  have huQ : u ∈ Q := hu ▸ Q.mul_mem hzQ hyQ
  have huC : ∀ a ∈ Q, Commute u a := fun a ha => hu ▸ (hzC a ha).mul_left (hyC a ha)
  have hxy : x * y * x⁻¹ = z := by
    have hxx : x * x = 1 := by simpa only [pow_two] using hx2
    calc
      x * y * x⁻¹ = (x * x) * z * (x⁻¹ * x⁻¹) := by dsimp only [y]; group
      _ = z := by rw [← mul_inv_rev, hxx, inv_one, one_mul, mul_one]
  have hxu : x * u * x⁻¹ = u := by
    rw [hu]
    calc
      x * (z * y) * x⁻¹ = (x * z * x⁻¹) * (x * y * x⁻¹) := by group
      _ = y * z := by rw [hxy]
      _ = z * y := hzy.symm.eq
  have hux : Commute u x := (mul_inv_eq_iff_eq_mul.mp hxu).symm
  have hEC : E ≤ centralizer ({u} : Set G) := by
    rw [hgen]
    refine sup_le ?_ (Subgroup.zpowers_le.mpr ?_)
    · intro a ha b hb
      have he : b = u := Set.mem_singleton_iff.mp hb
      subst b
      exact (huC a ha).eq
    · intro b hb
      have he : b = u := Set.mem_singleton_iff.mp hb
      subst b
      exact hux.eq
  have hune : u ≠ 1 := fun he => hnc (commutatorElement_eq_one_iff_commute.mp he)
  refine ⟨orderOf_eq_prime hu2 hune, ?_, ?_⟩
  · rw [hgen]
    exact (le_sup_left : Q ≤ Q ⊔ zpowers x) huQ
  · intro a ha
    exact hEC ha u (Set.mem_singleton u)

end Theory.GroupTheory
