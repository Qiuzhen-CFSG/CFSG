import Mathlib
import Submission.FeitThompson.FinalTheorem

/-!
# Odd core and quotient-center bridge

This module provides wrappers around `pPrimeCore 2 G` (the largest normal subgroup
of order coprime to 2, i.e., odd order) and lemmas connecting centrality in the
quotient to commutator membership.
-/

namespace Submission.ZStar

open Subgroup

section oddCoreDefinitions

variable (G : Type*) [Group G]

/-- The odd core `O(G) = O_{2'}(G)`: the largest normal subgroup of odd order. -/
abbrev oddCore : Subgroup G := pPrimeCore 2 G

end oddCoreDefinitions

section oddCoreProperties

variable (G : Type*) [Group G]

/-- The odd core is normal. -/
theorem oddCore_normal : (oddCore G).Normal :=
  pPrimeCore_normal (p := 2) (G := G)

end oddCoreProperties

section oddCoreCardinality

variable (G : Type*) [Group G] [Finite G]

/-- The odd core has odd cardinality. -/
theorem oddCore_odd : Odd (Nat.card (oddCore G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← Nat.coprime_two_left]
  simpa [oddCore] using pPrimeCore_coprime_card (p := 2) (G := G)

end oddCoreCardinality

section quotientCenterBridge

variable {G : Type*} [Group G] {N : Subgroup G} [N.Normal] {t : G}

/-- If `t` is central in the quotient by `N`, then all commutators `[g, t]` lie in `N`. -/
theorem commutators_mem_of_mem_center_quotient
    (ht : (QuotientGroup.mk' N t) ∈ Subgroup.center (G ⧸ N)) :
    ∀ g : G, g * t * g⁻¹ * t⁻¹ ∈ N := by
  intro g
  rw [Subgroup.mem_center_iff] at ht
  have h := ht (QuotientGroup.mk' N g)
  -- h: mk' N g * mk' N t = mk' N t * mk' N g, i.e., mk' N (g*t) = mk' N (t*g)
  have h_eq : QuotientGroup.mk' N (g * t) = QuotientGroup.mk' N (t * g) := by
    calc
      QuotientGroup.mk' N (g * t) = QuotientGroup.mk' N g * QuotientGroup.mk' N t := by simp
      _ = QuotientGroup.mk' N t * QuotientGroup.mk' N g := h
      _ = QuotientGroup.mk' N (t * g) := by simp
  -- mk' N a = mk' N b ↔ a / b ∈ N, and a / b = a * b⁻¹
  have hmem := (QuotientGroup.eq_iff_div_mem (x := g * t) (y := t * g)).mp h_eq
  -- hmem: (g*t) / (t*g) ∈ N, i.e., (g*t)*(t*g)⁻¹ ∈ N = g*t*g⁻¹*t⁻¹ ∈ N
  simpa [div_eq_mul_inv, mul_inv_rev, mul_assoc] using hmem

/-- The converse: if all commutators `[g, t]` lie in `N`, then `t` is central mod `N`. -/
theorem mem_center_quotient_of_commutators_mem
    (hcomm : ∀ g : G, g * t * g⁻¹ * t⁻¹ ∈ N) :
    (QuotientGroup.mk' N t) ∈ Subgroup.center (G ⧸ N) := by
  rw [Subgroup.mem_center_iff]
  intro x
  refine QuotientGroup.induction_on x (fun g => ?_)
  -- Need: (g*t) / (t*g) ∈ N, which expands to g*t*g⁻¹*t⁻¹ ∈ N, exactly hcomm g
  apply (QuotientGroup.eq_iff_div_mem (x := g * t) (y := t * g)).mpr
  simpa [div_eq_mul_inv, mul_inv_rev, mul_assoc] using hcomm g

/-- The equivalence: `t` is central in the quotient by `N` iff all commutators `[g, t]` lie in `N`. -/
theorem mem_center_quotient_iff_commutators_mem :
    (QuotientGroup.mk' N t ∈ Subgroup.center (G ⧸ N)) ↔
      ∀ g : G, g * t * g⁻¹ * t⁻¹ ∈ N := by
  constructor
  · exact commutators_mem_of_mem_center_quotient
  · exact mem_center_quotient_of_commutators_mem

end quotientCenterBridge

/-- The final packaging: if `t` maps to the center of `G / oddCore G`, then the Z* conclusion holds. -/
theorem conclusion_of_mem_center_oddCore
    {G : Type*} [Group G] [Finite G] {t : G}
    (ht : QuotientGroup.mk' (oddCore G) t ∈
      Subgroup.center (G ⧸ oddCore G)) :
    ∃ N : Subgroup G, N.Normal ∧ Odd (Nat.card N) ∧
      ∀ g : G, g * t * g⁻¹ * t⁻¹ ∈ N := by
  refine ⟨oddCore G, oddCore_normal G, oddCore_odd G, ?_⟩
  exact commutators_mem_of_mem_center_quotient ht

end Submission.ZStar
