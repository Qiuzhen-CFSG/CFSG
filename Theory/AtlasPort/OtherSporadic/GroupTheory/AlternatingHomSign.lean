/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/AlternatingHomSign.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# AlternatingHomSign

Every permutation representation of an alternating group has trivial sign.
Three-cycle generation and the orders of sign values prove the assertion.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/AlternatingHomSign.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for downstream calculations in the source API.
-/

@[expose] public section

namespace Atlas.GroupTheory
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem alternating_hom_sign (f : alternatingGroup α →* Equiv.Perm β)
    (g : alternatingGroup α) : Equiv.Perm.sign (f g) = 1 := by
  let h := Equiv.Perm.sign.comp f
  have htop : h.ker = ⊤ := by
    apply top_unique
    rw [← alternatingGroup.closure_isThreeCycles_eq_top, Subgroup.closure_le]
    intro x hx
    have hx3 : x ^ 3 = 1 := by
      apply Subtype.ext
      exact hx.orderOf ▸ pow_orderOf_eq_one x.val
    have hh : h x ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
    have hs := Int.units_sq (h x)
    change h x = 1
    calc
      h x = h x ^ 2 * h x := by rw [hs,one_mul]
      _ = 1 := by simpa only [pow_succ] using hh
  have hg : g ∈ h.ker := by rw [htop]; trivial
  exact hg

end Atlas.GroupTheory
