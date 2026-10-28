module
public import Theory.Frattini.PGroup
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Central Frattini subgroups from involutory commutators

If the derived subgroup of a finite two-group is central and has exponent
two, every square is central. The usual commutator-and-squares description
of the Frattini subgroup therefore puts it in the center. This applies to
the actual distance-four core in MS93 (4.6.9), without classifying its quotient.
-/

public section
namespace Subgroup
open scoped commutatorElement
variable {P : Type*} [Group P] [Finite P]

/-- Central commutators of exponent two force a finite two-group's Frattini subgroup to be central. -/
theorem frattini_le_center_of_central_involutory_commutators
    (hp : IsPGroup 2 P) (hc : _root_.commutator P ≤ center P)
    (hs : ∀ x ∈ _root_.commutator P, x ^ 2 = 1) : frattini P ≤ center P := by
  let : Fact (IsPGroup 2 P) := ⟨hp⟩
  rw [frattini_eq_closure_commutator_union_powers (p := 2)]
  apply (closure_le (K := center P)).mpr
  rintro x (hx | ⟨g, rfl⟩)
  · exact hc hx
  · apply mem_center_iff.mpr
    intro w
    have hcw : ⁅g,w⁆ ∈ _root_.commutator P :=
      commutator_mem_commutator (mem_top g) (mem_top w)
    have hfix : g * ⁅g,w⁆ * g⁻¹ = ⁅g,w⁆ := by
      rw [mem_center_iff.mp (hc hcw) g, mul_inv_cancel_right]
    have hh : ⁅g ^ 2,w⁆ = 1 := by
      rw [pow_two, commutatorElement_mul_left_eq_conj_mul, hfix, ← pow_two, hs _ hcw]
    exact (commutatorElement_eq_one_iff_mul_comm.mp hh).symm
end Subgroup
