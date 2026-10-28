module
public import Theory.GroupTheory.NormalizedSupCard
import Mathlib.Tactic.Group

/-!
# Cardinality of a disjoint permuting subgroup product

For permuting subgroups the set product is their join. Disjointness makes
multiplication a bijection from the Cartesian product to that join.
This is the order calculation for the odd subgroup times a Sylow two-group
in Aschbacher--Smith, A.3.15, printed pp.50--51.
-/

public section
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G]

/-- The join of permuting subgroups has their set product as carrier. -/
theorem coe_sup_eq_mul_of_permutes (H K : Subgroup G)
    (hp : (H : Set G) * (K : Set G) = (K : Set G) * (H : Set G)) :
    (↑(H ⊔ K) : Set G) = (H : Set G) * (K : Set G) := by
  let P : Subgroup G := {
    carrier := (H : Set G) * (K : Set G)
    one_mem' := ⟨1, H.one_mem, 1, K.one_mem, one_mul 1⟩
    mul_mem' := by
      rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
      have hbc : b * c ∈ (H : Set G) * (K : Set G) :=
        hp.symm ▸ Set.mul_mem_mul hb hc
      obtain ⟨c', hc', b', hb', he⟩ := hbc
      change c' * b' = b * c at he
      refine ⟨a * c', H.mul_mem ha hc', b' * d, K.mul_mem hb' hd, ?_⟩
      calc
        a * c' * (b' * d) = a * (c' * b') * d := by group
        _ = a * (b * c) * d := by rw [he]
        _ = a * b * (c * d) := by group
    inv_mem' := by
      rintro _ ⟨a, ha, b, hb, rfl⟩
      rw [mul_inv_rev]
      exact hp.symm ▸ Set.mul_mem_mul (K.inv_mem hb) (H.inv_mem ha) }
  have he : H ⊔ K = P := by
    apply le_antisymm
    · exact sup_le
        (fun a ha => ⟨a, ha, 1, K.one_mem, mul_one a⟩)
        (fun b hb => ⟨1, H.one_mem, b, hb, one_mul b⟩)
    · exact mul_subset (fun _ h => mem_sup_left h) (fun _ h => mem_sup_right h)
  rw [he]
  rfl

/-- Disjoint permuting subgroups have the expected product order. -/
theorem card_sup_eq_mul_of_permutes_of_disjoint (H K : Subgroup G)
    (hp : (H : Set G) * (K : Set G) = (K : Set G) * (H : Set G))
    (hd : Disjoint H K) : Nat.card (H ⊔ K : Subgroup G) = Nat.card H * Nat.card K := by
  let m : H × K → ↥(H ⊔ K) := fun p =>
    ⟨(p.1 : G) * (p.2 : G), mul_mem_sup p.1.property p.2.property⟩
  have hi : Function.Injective m := fun _ _ h =>
    mul_injective_of_disjoint hd (congrArg Subtype.val h)
  have hs : Function.Surjective m := by
    intro x
    have hx : (x : G) ∈ (H : Set G) * (K : Set G) := by
      rw [← coe_sup_eq_mul_of_permutes H K hp]
      exact x.property
    obtain ⟨a, ha, b, hb, hab⟩ := hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  exact (Nat.card_congr (Equiv.ofBijective m ⟨hi, hs⟩)).symm.trans (Nat.card_prod H K)

end Subgroup
