module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Data.Set.Card

/-!
# Centralizer order in a transitive nonidentity orbit

For a subgroup normalized by an actor, transitivity on its nonidentity
elements identifies the conjugacy orbit with the complement of one.
Orbit–stabilizer then computes the literal intersection centralizer.

This supplies the point-centralizer count in the Rudvalis argument of
Aschbacher–Smith, Theorem 4.2.13, printed pp.611–612.
-/

public section
namespace Theory.GroupAction
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Orbit-stabilizer on the actual nonidentity elements of a normalized subgroup. -/
theorem centralizer_card_mul_pred_of_transitive (B E : Subgroup G)
    (hBE : B ≤ normalizer (E : Set G))
    (ht : ∀ x ∈ E, ∀ y ∈ E, x ≠ 1 → y ≠ 1 → ∃ b ∈ B, b*x*b⁻¹ = y)
    (z : E) (hz : z ≠ 1) :
    Nat.card ((centralizer ({(z : G)} : Set G)).subgroupOf B) * (Nat.card E - 1) =
      Nat.card B := by
  let ρ : B →* MulAut E := E.normalizerMonoidHom.comp (inclusion hBE)
  let : MulDistribMulAction B E := MulDistribMulAction.compHom E ρ
  have horbit : MulAction.orbit B z = ({1} : Set E)ᶜ := by
    ext y
    constructor
    · rintro ⟨b,rfl⟩ hy
      change ρ b z = 1 at hy
      exact hz ((ρ b).injective (hy.trans (map_one (ρ b)).symm))
    · intro hy
      obtain ⟨b,hb,he⟩ := ht z z.property y y.property
        (fun h => hz (Subtype.ext h)) (fun h => hy (Subtype.ext h))
      exact ⟨⟨b,hb⟩,Subtype.ext he⟩
  have hcard : Nat.card (MulAction.orbit B z) = Nat.card E - 1 := by
    rw [horbit]
    change (({1} : Set E)ᶜ).ncard = _
    rw [Set.ncard_compl,Set.ncard_singleton]
  have hstab : MulAction.stabilizer B z = (centralizer ({(z : G)} : Set G)).subgroupOf B := by
    ext b
    change ρ b z = z ↔ (b : G) ∈ centralizer ({(z : G)} : Set G)
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro h
      have hh : (b : G)*z*(b : G)⁻¹ = z := congrArg Subtype.val h
      exact mul_inv_eq_iff_eq_mul.mp hh
    · intro h
      apply Subtype.ext
      change (b : G)*z*(b : G)⁻¹ = z
      rw [h,mul_inv_cancel_right]
  have hh := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup B z)
  rw [Nat.card_prod,hcard,hstab,Nat.mul_comm] at hh
  exact hh
end Theory.GroupAction
