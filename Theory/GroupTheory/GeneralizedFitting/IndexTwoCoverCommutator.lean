module

public import Theory.GroupTheory.GeneralizedFitting.IndexTwoCover

/-!
# The canonical subgroup in a quasisimple extension of index two

A perfect subgroup of index two is the full commutator subgroup: perfectness
gives one containment, and the cyclic quotient of order two gives the other.
Thus a normal quasisimple covering certificate can use the commutator as its
explicit witness, retaining its index and center order.

This identifies the canonical covering subgroup in the Held outer 2C row
of GLS3 Table 5.3p, with the covering convention on pp.260–261.
-/

public section

open Subgroup
namespace Theory.GroupTheory

variable {G : Type*} [Group G] {z : ℕ}

/-- The commutator itself witnesses a normal quasisimple extension of index two. -/
theorem HasQuasisimpleNormalOfIndexTwo.commutator
    (h : HasQuasisimpleNormalOfIndexTwo G z) :
    (commutator G).Normal ∧ IsQuasisimple (commutator G) ∧
      (commutator G).index = 2 ∧ Nat.card (center (commutator G)) = z := by
  obtain ⟨L, hn, hq, hi, hz⟩ := h
  let : L.Normal := hn
  let : IsQuasisimple L := hq
  let : IsCyclic (G ⧸ L) := isCyclic_of_prime_card hi
  have hL : L = _root_.commutator G := by
    apply le_antisymm
    · rw [← L.commutator_eq_self]
      exact Subgroup.commutator_mono le_top le_top
    · exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  rw [← hL]
  exact ⟨hn, hq, hi, hz⟩

end Theory.GroupTheory
