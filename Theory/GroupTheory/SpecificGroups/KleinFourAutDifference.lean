module
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# Automorphism differences in a Klein four group

Every element t of a Klein four group can be written as x⁻¹ * f(x) for an
automorphism f. Choose x outside {1,t}; then x and x*t are nonidentity,
so swapping them fixes the identity and defines a group automorphism.
The formula also covers t = 1, when the swap is the identity.

This elementary calculation supports the local focal arguments for
four-subgroups and Frattini quotients in Alperin--Brauer--Gorenstein,
Chapter II, Section 1, Propositions 1 and 2 (article pp.10--12). It is
independent of all ambient-group and classification hypotheses.
-/

namespace IsKleinFour
open scoped IsKleinFour

/-- Every element of a Klein four group is a difference between an element
and one of its automorphic images. -/
public theorem exists_mulAut_difference {H : Type*} [Group H] [IsKleinFour H]
    (t : H) : ∃ (x : H) (f : MulAut H), x⁻¹ * f x = t := by
  classical
  let : Fintype H := Fintype.ofFinite H
  have hcard : ({1, t} : Finset H).card < (Finset.univ : Finset H).card := by
    rw [Finset.card_univ, IsKleinFour.card_four']
    have hle := Finset.card_insert_le (1 : H) {t}
    simp only [Finset.card_singleton] at hle
    omega
  obtain ⟨x, _, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hx' : x ≠ 1 ∧ x ≠ t := by simpa using hx
  obtain ⟨hx1, hxt⟩ := hx'
  have hxt1 : x * t ≠ 1 := by
    intro h
    apply hxt
    simpa using eq_inv_of_mul_eq_one_left h
  let f : MulAut H := IsKleinFour.mulEquiv (Equiv.swap x (x * t)) (by
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hx1) (Ne.symm hxt1))
  refine ⟨x, f, ?_⟩
  change x⁻¹ * Equiv.swap x (x * t) x = t
  rw [Equiv.swap_apply_left, inv_mul_cancel_left]

end IsKleinFour
