module

public import Theory.Mathieu.M24.ValueBoundParabolics.QuotientBounds
public import Theory.Mathieu.M24.ValueBoundParabolics.SylowOvergroup
public import Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.Reduction
public import Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.Order
public import Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.Automorphisms

/-!
# Certification of the local quotients for the M₂₄ value bound

The marked subgroup has checked order 1024 and is a self-normalizing Sylow
subgroup. Thus every overgroup of order 3072 has relative index three and
intrinsic two-core quotient S₃; it is proper in M₂₄. These deductions need
only the order and containment of a proposed overgroup.

Constructing three such overgroups and proving that they generate M₂₄ is
still required. This module does not assume that construction in a definition
or assert its existence.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, E.4.3(2),
printed p. 242 (PDF p. 253).
-/

public section
open Subgroup Theory.GroupTheory
namespace Sporadic.Mathieu.M24ValueBoundParabolics
open M24LocalGeometry.SylowNormalizer

/-- The intrinsic quotient of an order-3072 overgroup of the marked Sylow subgroup. -/
theorem candidate_overgroup_quotient (H : Subgroup M24) (hSH : candidate ≤ H)
    (hH : Nat.card H = 3072) :
    Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) := by
  have hs : Nat.card candidate = 2 ^ (Nat.card M24).factorization 2 := by
    rw [candidate_card, m24_order]
    decide +kernel
  let S : Sylow 2 M24 := Sylow.ofCard candidate hs
  have hS : (S : Subgroup M24) = candidate := Sylow.coe_ofCard candidate hs
  apply symmetricThree_quotient_of_selfNormalizing_sylow S
    (sylow_normalizer_le candidate_card
      (candidate_automorphisms_isPGroup candidate_card) _) H (hS ▸ hSH)
  rw [hS]
  have hi := (candidate.subgroupOf H).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hSH).toEquiv, candidate_card, hH] at hi
  change candidate.relIndex H * 1024 = 3072 at hi
  omega

/-- The order-3072 overgroups used by the construction are proper. -/
theorem candidate_overgroup_lt_top (H : Subgroup M24) (hH : Nat.card H = 3072) :
    H < ⊤ := by
  apply lt_of_le_of_ne le_top
  intro he
  have hc : Nat.card H = Nat.card M24 :=
    Nat.card_congr ((MulEquiv.subgroupCongr he).trans Subgroup.topEquiv).toEquiv
  rw [hH, m24_order] at hc
  contradiction

end Sporadic.Mathieu.M24ValueBoundParabolics
