module

public import Mathlib.GroupTheory.Perm.Closure
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic.FinCases

/-!
# Three even-conjugate triple transpositions generate S₇

Take `(01)(23)(45)`, `(12)(34)(56)`, and `(12)(35)(46)`. The product
of the first two is a seven-cycle; the cube of the product of all three
is `(01)`. A prime cycle and a transposition generate the symmetric group.
Explicit even conjugators connect all three to the first generator.
Only these small permutation identities use kernel reduction.

This supplies the permutation part of the maximal S₇ argument in
Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
manuscript pp.10–11. It does not assert a unitary embedding.
-/

public section
open Equiv Subgroup
namespace BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five.Outer

/-- The marked odd involution for the concrete semilinear embedding. -/
@[expose] def tripleSwap : Perm (Fin 7) := swap 0 1 * swap 2 3 * swap 4 5

private def second : Perm (Fin 7) := swap 1 2 * swap 3 4 * swap 5 6
private def third : Perm (Fin 7) := swap 1 2 * swap 3 5 * swap 4 6

/-- Three generators in a single orbit under the alternating group. -/
@[expose] def generators : Fin 3 → Perm (Fin 7) :=
  ![tripleSwap, swap 1 2 * swap 3 4 * swap 5 6, swap 1 2 * swap 3 5 * swap 4 6]

theorem generators_generate : closure (Set.range generators) = ⊤ := by
  let H := closure (Set.range generators)
  have ha : tripleSwap ∈ H := subset_closure ⟨0, rfl⟩
  have hb : second ∈ H := subset_closure ⟨1, rfl⟩
  have hc : third ∈ H := subset_closure ⟨2, rfl⟩
  have hswap : swap (0 : Fin 7) 1 ∈ H := by
    have he : (tripleSwap * second * third) ^ 3 = swap (0 : Fin 7) 1 := by
      decide +kernel
    exact he ▸ H.pow_mem (H.mul_mem (H.mul_mem ha hb) hc) 3
  have hgen := Perm.closure_prime_cycle_swap
    (by decide : (Fintype.card (Fin 7)).Prime)
    (by rw [← Perm.card_cycleType_eq_one]; decide +kernel : (tripleSwap * second).IsCycle)
    (by decide +kernel : (tripleSwap * second).support = Finset.univ)
    (show (swap (0 : Fin 7) 1).IsSwap from ⟨0, 1, by decide, rfl⟩)
  apply top_unique
  rw [← hgen]
  exact (closure_le _).mpr (Set.insert_subset_iff.mpr
    ⟨H.mul_mem ha hb, Set.singleton_subset_iff.mpr hswap⟩)

private def evenSecond : alternatingGroup (Fin 7) :=
  ⟨swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4 * swap 4 5 * swap 5 6,
    by rw [Perm.mem_alternatingGroup]; decide +kernel⟩

private def evenThird : alternatingGroup (Fin 7) :=
  ⟨swap 0 1 * swap 1 2 * swap 2 3 * swap 3 5 * swap 5 4 * swap 4 6,
    by rw [Perm.mem_alternatingGroup]; decide +kernel⟩

/-- The conjugators have even sign, so an embedding mapping A₇ into the
inner automorphisms supplies literal PSU₃ conjugators. -/
theorem generators_even_conjugate (i : Fin 3) :
    ∃ q : alternatingGroup (Fin 7),
      (q : Perm (Fin 7)) * tripleSwap * (q : Perm (Fin 7))⁻¹ = generators i := by
  fin_cases i
  · exact ⟨1, by simp [generators]⟩
  · exact ⟨evenSecond, by decide +kernel⟩
  · exact ⟨evenThird, by decide +kernel⟩

end BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five.Outer
