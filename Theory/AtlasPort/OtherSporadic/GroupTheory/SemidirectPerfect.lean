/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/SemidirectPerfect.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.IsPerfect

/-!
# Perfect semidirect products

An explicit commutator calculation proves perfectness when the acting group is perfect and every normal-factor element is an action difference.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/SemidirectPerfect.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
-/

@[expose] public section

/-!
# Perfectness of semidirect products from action commutators

This criterion is independent of the finite simple group constructions.
-/

namespace Atlas.GroupTheory

open SemidirectProduct
open scoped commutatorElement

/-- If the acting group is perfect and every element of the normal factor
is an action commutator, the full semidirect product is perfect. -/
theorem semidirect_isPerfect_of_action_differences
    {N P : Type*} [Group N] [Group P] [Group.IsPerfect P]
    (φ : P →* MulAut N)
    (hdiff : ∀ n : N, ∃ p : P, ∃ w : N, φ p w * w⁻¹ = n) :
    Group.IsPerfect (N ⋊[φ] P) := by
  constructor
  apply top_unique
  intro x _
  have hl : ∀ n : N, (inl n : N ⋊[φ] P) ∈ commutator (N ⋊[φ] P) := by
    intro n
    obtain ⟨p, w, rfl⟩ := hdiff n
    have he : (inl (φ p w * w⁻¹) : N ⋊[φ] P) =
        ⁅(inr p : N ⋊[φ] P), inl w⁆ := by
      rw [map_mul, map_inv, inl_aut]
      simp only [commutatorElement_def, map_inv]
    rw [he]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hr : ∀ p : P, (inr p : N ⋊[φ] P) ∈ commutator (N ⋊[φ] P) := by
    intro p
    have hp := Group.IsPerfect.mem_commutator (g := p)
    have hm := Subgroup.mem_map_of_mem (inr : P →* N ⋊[φ] P) hp
    rw [map_commutator_eq] at hm
    exact (Subgroup.commutator_mono le_top le_top) hm
  rw [← inl_left_mul_inr_right x]
  exact (commutator (N ⋊[φ] P)).mul_mem (hl x.left) (hr x.right)

end Atlas.GroupTheory
