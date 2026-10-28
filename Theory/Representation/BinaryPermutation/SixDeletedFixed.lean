module

public import Theory.Representation.BinaryPermutation.OffenderFixedSpace
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# No fixed vector in the deleted six-point A6 module

Two five-cycles with different fixed points force a representative of an
invariant deleted vector to be constant. Each cycle fixes a coordinate, so
fixation modulo constants lifts to fixation on the full permutation module.
The native M22 hexad applies this to its cocode fixed space.
Source: Aschbacher--Smith H.15.2(2), used in 8.2.11, pp.398,722.
-/

public section
namespace BinaryPermutation

private def cycleA : Equiv.Perm (Fin 6) :=
  Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4

private def cycleB : Equiv.Perm (Fin 6) :=
  Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 5

private theorem cycleA_even : cycleA ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

private theorem cycleB_even : cycleB ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

theorem sixDeleted_fixed_eq_zero (v : Deleted (Fin 6))
    (hv : ∀ g : alternatingGroup (Fin 6), deletedRepresentation (Fin 6) g.val v = v) :
    v = 0 := by
  obtain ⟨w, rfl⟩ := (constants (Fin 6)).mkQ_surjective v
  have ha := (deleted_fixed_iff_of_fixed_point cycleA w 5 (by decide +kernel)).mp
    (hv ⟨cycleA, cycleA_even⟩)
  have hb := (deleted_fixed_iff_of_fixed_point cycleB w 4 (by decide +kernel)).mp
    (hv ⟨cycleB, cycleB_even⟩)
  have hc : w = fun _ => w 0 := by
    have h : ∀ w : Full (Fin 6), representation (Fin 6) cycleA w = w →
        representation (Fin 6) cycleB w = w → w = fun _ => w 0 := by decide +kernel
    exact h w ha hb
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact Submodule.mem_span_singleton.mpr ⟨w 0, by
    ext i
    simpa [allOne] using (congrFun hc i).symm⟩

end BinaryPermutation
