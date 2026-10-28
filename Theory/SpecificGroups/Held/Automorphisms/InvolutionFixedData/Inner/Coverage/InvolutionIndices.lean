module

public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.Coverage.FiniteData

/-!
# Exhaustive selection of possible involutions among the Held binary words

For each of the 1024 binary indices, the kernel checks one of three facts:
the index is zero; its permutation square moves a specified point; or it
occurs in the 191-entry forest. The first two alternatives cannot have order
two. Thus every involution among the binary words occurs in the finite list.

This does not assert surjectivity of the binary words onto the representative,
or conjugacy of the selected entries. Those are independent obligations.
Source: GLS3 Table 5.3p; ATLAS HeG1-p2058B0 and `Source/discovery.json`.
-/

namespace Held.InvolutionFixedData.Coverage
open TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration

private theorem checkedAll {m : ℕ} (P : Fin m → Prop) [DecidablePred P]
    (h : (List.finRange m).all (fun i => decide (P i)) = true) : ∀ i, P i := by
  intro i
  exact of_decide_eq_true (List.all_eq_true.mp h i (by simp))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem index_cases (n : Fin 1024) :
    n = 0 ∨
      normalPerm n (normalPerm n (squareWitness n)) ≠ squareWitness n ∨
      forestIndex (forestRow n) = n := by
  have h : ∀ n : Fin 1024,
      n = 0 ∨
        normalPerm n (normalPerm n (squareWitness n)) ≠ squareWitness n ∨
        forestIndex (forestRow n) = n := by
    apply checkedAll
    decide +kernel
  exact h n

/-- The exhaustive square checks reduce every binary involution to one of
the 191 selected indices. No surjectivity or fusion premise is needed here. -/
public theorem normalForm_involution_index (n : Fin 1024)
    (hn : orderOf (normalForm n).val = 2) :
    ∃ i : Fin 191, forestIndex i = n := by
  rcases index_cases n with rfl | hmove | hrow
  · rw [normalForm_zero, orderOf_one] at hn
    contradiction
  · have hp : (normalForm n).val ^ 2 = 1 := by
      rw [← hn]
      exact pow_orderOf_eq_one _
    have hperm : normalPerm n ^ 2 = 1 := by
      rw [← normalForm_representation, ← map_pow, hp, map_one]
    apply False.elim
    apply hmove
    change (normalPerm n ^ 2) (squareWitness n) = _
    rw [hperm]
    rfl
  · exact ⟨forestRow n, hrow⟩

end Held.InvolutionFixedData.Coverage
