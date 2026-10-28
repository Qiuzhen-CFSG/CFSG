/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/PrimeFreePermutation.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# PrimeFreePermutation

A fixed-point-free permutation of prime exponent forces that prime to divide the degree.
Its cycle decomposition consists entirely of cycles of that prime length.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/PrimeFreePermutation.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for downstream calculations in the source API.
-/

@[expose] public section

namespace Atlas.GroupTheory

/-- A permutation of prime exponent without fixed points partitions a finite set
into cycles of that prime length. -/
theorem prime_dvd_card_of_fixedPointFree {X : Type*} [Fintype X] [DecidableEq X]
    (g : Equiv.Perm X) (p : ℕ) (hp : p.Prime) (hg : g ^ p = 1)
    (hf : ∀ x, g x ≠ x) : p ∣ Fintype.card X := by
  let : Fact p.Prime := ⟨hp⟩
  have hs : g.support = Finset.univ := by
    ext x
    simp [Equiv.Perm.mem_support,hf x]
  have he := Equiv.Perm.cycleType_of_pow_prime_eq_one hg
  have hc := g.sum_cycleType
  rw [he,Multiset.sum_replicate,hs,Finset.card_univ] at hc
  exact ⟨g.cycleType.card,by simpa [mul_comm] using hc.symm⟩

end Atlas.GroupTheory
