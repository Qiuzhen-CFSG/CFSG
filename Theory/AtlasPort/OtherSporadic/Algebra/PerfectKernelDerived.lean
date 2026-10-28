/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/PerfectKernelDerived.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.Data.ZMod.Basic

/-!
# Perfect kernels and derived subgroups

A perfect kernel of a homomorphism to an abelian group equals the derived
subgroup. Surjective binary parity also gives kernel index two.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/PerfectKernelDerived.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and rewritten project imports.
Definitions remain exposed for downstream calculations.
-/

@[expose] public section

namespace Atlas.Algebra

/-- A perfect kernel with abelian quotient is precisely the derived subgroup. -/
theorem commutator_eq_perfect_kernel {G A : Type*} [Group G] [CommGroup A]
    (f : G →* A) [Group.IsPerfect f.ker] : commutator G=f.ker := by
  apply le_antisymm (Abelianization.commutator_subset_ker f)
  rw [← f.ker.commutator_eq_self]
  exact Subgroup.commutator_mono le_top le_top

/-- Surjective actual binary parity has kernel index two, without knowing the
ambient group order. -/
theorem binary_parity_kernel_index {G : Type*} [Group G]
    (f : G →* Multiplicative (ZMod 2)) (hf : Function.Surjective f) : f.ker.index=2 := by
  rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr hf,Subgroup.card_top,Nat.card_eq_fintype_card]
  rfl

end Atlas.Algebra
