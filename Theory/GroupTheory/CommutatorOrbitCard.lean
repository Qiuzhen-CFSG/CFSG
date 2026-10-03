module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic

/-!
# A commutator subgroup bounds a conjugacy orbit

The orbit of `y` under a subgroup `R`, translated by `y⁻¹`, embeds in
`[R, ⟨y⟩]`. Orbit-stabilizer therefore bounds `|R|` by the product of
the commutator order and the relative centralizer order. This is the
elementary orbit count used in Thompson VI, printed p.630.
-/

namespace Subgroup
open scoped commutatorElement

/-- Translation embeds the relative conjugacy orbit into the commutator subgroup. -/
public theorem card_le_commutator_card_mul_centralizer
    {G : Type*} [Group G] [Finite G] (R : Subgroup G) (y : G) :
    Nat.card R ≤ Nat.card (⁅R, zpowers y⁆ : Subgroup G) *
      Nat.card ((centralizer ({y} : Set G)).subgroupOf R) := by
  let _ : MulAction R G := {
    smul := fun r t => (r : G) * t * (r : G)⁻¹
    one_smul := by intro t; change (1 : G) * t * (1 : G)⁻¹ = t; simp
    mul_smul := by
      intro a b t
      change ((a : G) * (b : G)) * t * ((a : G) * (b : G))⁻¹ =
        (a : G) * ((b : G) * t * (b : G)⁻¹) * (a : G)⁻¹
      simp [mul_assoc] }
  have hstab : MulAction.stabilizer R y =
      (centralizer ({y} : Set G)).subgroupOf R := by
    ext r
    rw [MulAction.mem_stabilizer_iff]
    change (r : G) * y * (r : G)⁻¹ = y ↔ _
    rw [mul_inv_eq_iff_eq_mul]
    exact mem_centralizer_singleton_iff.symm
  let f : MulAction.orbit R y → ↥(⁅R, zpowers y⁆ : Subgroup G) := fun t =>
    ⟨(t : G) * y⁻¹, by
      obtain ⟨r, hr⟩ := t.property
      change (r : G) * y * (r : G)⁻¹ = (t : G) at hr
      rw [← hr]
      exact commutator_mem_commutator r.property (mem_zpowers y)⟩
  have hf : Function.Injective f := by
    intro a b h
    exact Subtype.ext (mul_right_cancel (congrArg Subtype.val h))
  have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup R y)
  rw [Nat.card_prod, hstab] at hc
  rw [← hc]
  exact Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective f hf)

end Subgroup
