/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/SixteenEightObstruction.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Lean.Elab.Tactic.Omega
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# SixteenEightObstruction

A group of order sixteen acting on eight points with uniform fixed-point counts
for nonidentity elements acts trivially. Orbit counting forces each element to fix every point.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/SixteenEightObstruction.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for downstream calculations in the source API.
-/

@[expose] public section

namespace Atlas.GroupTheory
open MulAction Finset

variable {U X : Type*} [Group U] [Finite U] [Finite X] [MulAction U X]

theorem sixteen_eight_fixed (hu : Nat.card U = 16) (hx : Nat.card X = 8)
    (f : ℕ) (uniform : ∀ u : U, u ≠ 1 → Nat.card (fixedBy X u) = f) :
    ∀ u : U, ∀ x : X, u • x = x := by
  classical
  let := Fintype.ofFinite U
  let := Fintype.ofFinite X
  let (u : U) : Fintype (fixedBy X u) := Fintype.ofFinite _
  let := Fintype.ofFinite (Quotient (orbitRel U X))
  have hn : ∃ u : U, u ≠ 1 := by
    have : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    exact exists_ne 1
  obtain ⟨v,hv⟩ := hn
  have hf : f ≤ 8 := by
    rw [← uniform v hv,← hx]
    exact Nat.card_le_card_of_injective _ Subtype.val_injective
  have hsum : (∑ u : U, Fintype.card (fixedBy X u)) = 8 + 15*f := by
    rw [← sum_erase_add _ _ (mem_univ (1 : U))]
    have he : ∑ u ∈ univ.erase (1 : U), Fintype.card (fixedBy X u) = 15*f := by
      calc
        _ = ∑ _u ∈ univ.erase (1 : U), f := by
          apply sum_congr rfl
          intro u hu'
          exact (Nat.card_eq_fintype_card).symm.trans (uniform u (mem_erase.mp hu').1)
        _ = 15*f := by simp [← Nat.card_eq_fintype_card,hu]
    rw [he]
    have h1 : Fintype.card (fixedBy X (1 : U)) = 8 := by
      have he : fixedBy X (1 : U) = Set.univ := by ext x; simp [fixedBy]
      rw [← Nat.card_eq_fintype_card,he]
      exact (Nat.card_congr (Equiv.Set.univ X)).trans hx
    rw [h1,add_comm]
  have hb := sum_card_fixedBy_eq_card_orbits_mul_card_group U X
  rw [hsum,← Nat.card_eq_fintype_card (α := U),hu] at hb
  have hf8 : f = 8 := by omega
  intro u x
  by_cases he : u = 1
  · subst u; exact one_smul U x
  have hc : Nat.card (fixedBy X u) = Nat.card X := by rw [uniform u he,hf8,hx]
  have hs : Function.Surjective (Subtype.val : fixedBy X u → X) :=
    (Nat.bijective_iff_injective_and_card _).mpr ⟨Subtype.val_injective,hc⟩ |>.2
  obtain ⟨y,hy⟩ := hs x
  exact hy ▸ y.prop

end Atlas.GroupTheory
