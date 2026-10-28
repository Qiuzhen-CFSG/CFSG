module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Tactic.Group

/-!
# Quaternion relations from a central two-group triple

Suppose three group elements have product one and the same square in a
central two-subgroup. Their first two elements satisfy the quaternion
relations: the first has fourth power one, and the second conjugates it
to its inverse. No restriction is placed on the order of the central
subgroup, and the common square is allowed to be trivial.

The square of the product determines the conjugation relation up to a
central square. Squaring that conjugation shows the common square has
sixth power one. The cube map on a two-group is injective, so its square
is one, giving the claimed relations. In a central extension of A4,
these triples arise from cyclic conjugation by an order-three lift.

This is the elementary arbitrary-kernel calculation behind the q=3
Schur-cover step used in ABG II.3 Proposition 2, article p.22,
`refs/latex/alperin-brauer-gorenstein-pages/page-023.tex`.
-/

public section

namespace QuaternionGroup

theorem quaternion_relations_of_central_two_triple
    {E : Type*} [Group E] (Z : Subgroup E)
    (hZcenter : Z ≤ Subgroup.center E) (hZtwo : IsPGroup 2 Z)
    (a b c s : E) (hs : s ∈ Z)
    (ha : a ^ 2 = s) (hb : b ^ 2 = s) (hc : c ^ 2 = s)
    (habc : a * b * c = 1) :
    a ^ 4 = 1 ∧ b * a = a⁻¹ * b := by
  have hscomm (x : E) : Commute s x :=
    (Subgroup.mem_center_iff.mp (hZcenter hs) x).symm
  have habsq : (a * b) ^ 2 = s⁻¹ := by
    have hc' : c = (a * b)⁻¹ := eq_inv_of_mul_eq_one_right habc
    rw [hc', inv_pow] at hc
    exact inv_eq_iff_eq_inv.mp hc
  have hconj : b * a * b⁻¹ = a⁻¹ * (s⁻¹) ^ 2 := by
    calc
      b * a * b⁻¹ = a⁻¹ * (a * b) ^ 2 * (b ^ 2)⁻¹ := by
        simp only [pow_two]
        group
      _ = a⁻¹ * s⁻¹ * s⁻¹ := by rw [habsq, hb]
      _ = a⁻¹ * (s⁻¹) ^ 2 := by group
  have hconjsq : (b * a * b⁻¹) ^ 2 = s := by
    calc
      (b * a * b⁻¹) ^ 2 = b * a ^ 2 * b⁻¹ := by
        simp only [pow_two]
        group
      _ = b * s * b⁻¹ := by rw [ha]
      _ = s := by rw [← (hscomm b).eq]; group
  have hcomm : Commute a⁻¹ ((s⁻¹) ^ 2) :=
    ((hscomm a).symm.inv_left.inv_right).pow_right 2
  rw [hconj, hcomm.mul_pow, inv_pow, ha] at hconjsq
  have hs6 : s ^ 6 = 1 := by
    have h := congrArg (fun x : E => s ^ 5 * x) hconjsq
    group at h
    exact_mod_cast h.symm
  have hs2Z : (⟨s, hs⟩ : Z) ^ 2 = 1 := by
    apply (hZtwo.powEquiv (by decide : Nat.Coprime 2 3)).injective
    apply Subtype.ext
    change (s ^ 2) ^ 3 = (1 : E) ^ 3
    rw [← pow_mul, hs6, one_pow]
  have hs2 : s ^ 2 = 1 := congrArg Subtype.val hs2Z
  constructor
  · calc
      a ^ 4 = (a ^ 2) ^ 2 := by group
      _ = 1 := by rw [ha, hs2]
  · have hconj' : b * a * b⁻¹ = a⁻¹ := by
      simpa only [inv_pow, hs2, inv_one, mul_one] using hconj
    calc
      b * a = (b * a * b⁻¹) * b := by group
      _ = a⁻¹ * b := by rw [hconj']

end QuaternionGroup

