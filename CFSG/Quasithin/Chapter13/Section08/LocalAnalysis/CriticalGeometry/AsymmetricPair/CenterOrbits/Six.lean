module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# Nonzero orbits and square swaps in the six-letter natural module

The fifteen duads exhaust the nonzero vectors of the actual quotient of the
permutation core. Double transitivity moves any duad to any other. In the
marked plane, the even involutions (40)(51) and (42)(53) interchange the
marked vector e₄₅ with e₀₁ and e₂₃. The identity handles e₄₅ itself. Thus the
alternating parabolic already contains every square-swap needed below.

`BinaryFlags.L2` is the full alternating plane stabilizer, not the source's
two-residual L₂. The marked-action adapter identifies the image of L₂T with
this full parabolic (or the symmetric parabolic); it never identifies the
source residual with the full stabilizer.

Source: Aschbacher–Smith, Notation 13.2.1 and the sufficiency of (*) in 13.8.7,
printed pp.877, 949.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair
namespace SixCenterGeometry
open Theory.SpecificGroups.SymmetricSix
open BinaryFlags NaturalGeometry BinaryPermutation

theorem nonzero_transitive (x y : natural (Fin 6)) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ g : Equiv.Perm (Fin 6), naturalRepresentation _ g x = y := by
  obtain ⟨d, rfl⟩ := (vector_cases x).resolve_left hx
  obtain ⟨e, rfl⟩ := (vector_cases y).resolve_left hy
  have hd : d.val.1 ≠ d.val.2 := ne_of_lt d.property
  have he : e.val.1 ≠ e.val.2 := ne_of_lt e.property
  obtain ⟨g, hg1, hg2⟩ := (MulAction.is_two_pretransitive_iff.mp
    (Equiv.Perm.isMultiplyPretransitive (Fin 6) 2))
      hd he
  refine ⟨g, ?_⟩
  change naturalRepresentation _ g (pairVector d.val.1 d.val.2) = _
  rw [pairVector_map]
  exact congrArg₂ pairVector hg1 hg2

private def exchange01 : Equiv.Perm (Fin 6) := Equiv.swap 4 0 * Equiv.swap 5 1
private def exchange23 : Equiv.Perm (Fin 6) := Equiv.swap 4 2 * Equiv.swap 5 3

private theorem exchange01_mem : exchange01 ∈ BinaryFlags.L2 := by
  change exchange01 ∈ H2 ∧ Equiv.Perm.sign exchange01 = 1
  decide
private theorem exchange23_mem : exchange23 ∈ BinaryFlags.L2 := by
  change exchange23 ∈ H2 ∧ Equiv.Perm.sign exchange23 = 1
  decide
private theorem exchange01_sq : exchange01 ^ 2 = 1 := by decide
private theorem exchange23_sq : exchange23 ^ 2 = 1 := by decide

/-- The marked alternating parabolic already contains the required involutions. -/
theorem square_swap (v : natural (Fin 6)) (hv : v ∈ canonicalPlane) (hne : v ≠ 0) :
    ∃ s ∈ BinaryFlags.L2, s ^ 2 = 1 ∧
      naturalRepresentation _ s (pairVector 4 5) = v := by
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hv
  fin_cases a <;> fin_cases b
  all_goals simp only [show (⟨0, by decide⟩ : Fin 2) = (0 : ZMod 2) from rfl,
    show (⟨1, by decide⟩ : Fin 2) = (1 : ZMod 2) from rfl,
    zero_smul, one_smul, zero_add, add_zero] at hab
  · exact False.elim (hne hab.symm)
  · refine ⟨exchange23, exchange23_mem, exchange23_sq, ?_⟩
    rw [pairVector_map]
    exact hab
  · refine ⟨exchange01, exchange01_mem, exchange01_sq, ?_⟩
    rw [pairVector_map]
    exact hab
  · refine ⟨1, BinaryFlags.L2.one_mem, one_pow _, ?_⟩
    simpa only [map_one, Module.End.one_apply, pairVector_add] using hab

end SixCenterGeometry
end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair

end
